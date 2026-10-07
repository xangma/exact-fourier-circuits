"""Sparse GF(2) directions and lazy orthonormal complement frames.

Dot products use the standard symmetric bilinear form. A vector's norm is its
weight modulo two. Tensor indices use row-major (last factor varies fastest).
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from math import prod
from typing import Iterable, Iterator, Sequence


def _integer(value: object, name: str, minimum: int = 0) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < minimum:
        raise ValueError(f"{name} must be an integer at least {minimum}")
    return value


class NoOrthonormalBasisError(ValueError):
    """The positive-dimensional complement is alternating (all norms zero)."""


@dataclass(frozen=True)
class SparseBinaryVector:
    dimension: int
    ones: tuple[int, ...]

    def __post_init__(self) -> None:
        _integer(self.dimension, "dimension")
        ones = tuple(self.ones)
        previous = -1
        for index in ones:
            _integer(index, "support index")
            if index >= self.dimension:
                raise ValueError(f"support index {index} is outside dimension {self.dimension}")
            if index <= previous:
                raise ValueError("support indices must be strictly increasing")
            previous = index
        object.__setattr__(self, "ones", ones)

    @classmethod
    def from_indices(cls, dimension: int, indices: Iterable[int]) -> SparseBinaryVector:
        """Canonical support from unordered distinct indices; duplicates fail."""
        indices = tuple(indices)
        if len(set(indices)) != len(indices):
            raise ValueError("duplicate support indices")
        return cls(dimension, tuple(sorted(indices)))

    @classmethod
    def unit(cls, dimension: int, index: int) -> SparseBinaryVector:
        return cls(dimension, (index,))

    @classmethod
    def zero(cls, dimension: int) -> SparseBinaryVector:
        return cls(dimension, ())

    @property
    def weight(self) -> int:
        return len(self.ones)

    @property
    def norm(self) -> int:
        return self.weight & 1

    @property
    def weight_mod4(self) -> int:
        return self.weight & 3

    def contains(self, index: int) -> bool:
        _integer(index, "coordinate")
        if index >= self.dimension:
            raise ValueError("coordinate outside vector dimension")
        # Binary search avoids an allocation even for large sparse supports.
        low, high = 0, len(self.ones)
        while low < high:
            middle = (low + high) // 2
            if self.ones[middle] < index:
                low = middle + 1
            else:
                high = middle
        return low < len(self.ones) and self.ones[low] == index

    def iter_ones(self) -> Iterator[int]:
        return iter(self.ones)

    def _same_dimension(self, other: SparseBinaryVector) -> None:
        if not isinstance(other, SparseBinaryVector) or other.dimension != self.dimension:
            raise ValueError("binary vectors must have the same dimension")

    def dot(self, other: SparseBinaryVector) -> int:
        self._same_dimension(other)
        i = j = parity = 0
        while i < self.weight and j < other.weight:
            left, right = self.ones[i], other.ones[j]
            if left == right:
                parity ^= 1
                i += 1
                j += 1
            elif left < right:
                i += 1
            else:
                j += 1
        return parity

    def xor(self, other: SparseBinaryVector) -> SparseBinaryVector:
        self._same_dimension(other)
        i = j = 0
        support = []
        while i < self.weight and j < other.weight:
            left, right = self.ones[i], other.ones[j]
            if left == right:
                i += 1
                j += 1
            elif left < right:
                support.append(left)
                i += 1
            else:
                support.append(right)
                j += 1
        support.extend(self.ones[i:])
        support.extend(other.ones[j:])
        return type(self)(self.dimension, tuple(support))

    __xor__ = xor


def transvection(direction: SparseBinaryVector, vector: SparseBinaryVector) -> SparseBinaryVector:
    """T_v(x) = x + v (v dot x); isotropic v makes T_v orthogonal."""
    direction._same_dimension(vector)
    if direction.norm:
        raise ValueError("orthogonal transvection direction must have norm zero")
    return vector.xor(direction) if direction.dot(vector) else vector


def full_coordinate_basis(dimension: int) -> Iterator[SparseBinaryVector]:
    """Lazy standard basis, with no dimension-by-dimension dense allocation."""
    _integer(dimension, "dimension")
    for index in range(dimension):
        yield SparseBinaryVector.unit(dimension, index)


def _first_missing(vector: SparseBinaryVector, excluded: Sequence[int] = ()) -> int | None:
    # At most weight+len(excluded)+1 indices are visited, even if dimension is huge.
    blocked = set(excluded)
    candidate = cursor = 0
    while candidate < vector.dimension:
        while cursor < vector.weight and vector.ones[cursor] < candidate:
            cursor += 1
        if candidate not in blocked and (cursor == vector.weight or vector.ones[cursor] != candidate):
            return candidate
        candidate += 1
    return None


def orthonormal_basis_complement(vectors: Sequence[SparseBinaryVector]) -> Iterator[SparseBinaryVector]:
    """Lazily extend one or two prescribed orthonormal vectors.

    With one vector u choose u_p=0, v=e_p+u, so T_v(e_p)=u.
    With two vectors u,y, let w=T_v(y), choose q!=p with w_q=0,
    and v2=e_q+w. Then O=T_v T_v2 maps e_p to u and e_q to y;
    O(e_j), j outside p,q, is the required complement frame.

    Failure to find p/q precisely identifies an alternating complement: its
    prescribed span contains the all-ones characteristic vector. If the
    complement dimension is positive, every vector in it has norm zero and
    no orthonormal basis exists. A zero-dimensional complement is valid.
    """
    vectors = tuple(vectors)
    if len(vectors) not in (1, 2):
        raise ValueError("one or two prescribed orthonormal vectors are required")
    if any(not isinstance(vector, SparseBinaryVector) for vector in vectors):
        raise ValueError("prescribed vectors must be SparseBinaryVector instances")
    dimension = vectors[0].dimension
    if any(vector.dimension != dimension for vector in vectors):
        raise ValueError("prescribed vectors must have the same dimension")
    if any(vector.norm != 1 for vector in vectors):
        raise ValueError("prescribed vectors must have norm one")
    if len(vectors) == 2 and vectors[0].dot(vectors[1]):
        raise ValueError("prescribed vectors must be orthogonal")
    if dimension == len(vectors):
        return
    u = vectors[0]
    p = _first_missing(u)
    if p is None:
        raise NoOrthonormalBasisError("positive-dimensional complement is alternating: u is all ones")
    first_direction = SparseBinaryVector.unit(dimension, p).xor(u)
    q = None
    second_direction = None
    if len(vectors) == 2:
        w = transvection(first_direction, vectors[1])
        q = _first_missing(w, (p,))
        if q is None:
            raise NoOrthonormalBasisError(
                "positive-dimensional complement is alternating: u+y is all ones")
        second_direction = SparseBinaryVector.unit(dimension, q).xor(w)
    for index in range(dimension):
        if index == p or index == q:
            continue
        vector = SparseBinaryVector.unit(dimension, index)
        if second_direction is not None:
            vector = transvection(second_direction, vector)
        yield transvection(first_direction, vector)


@dataclass(frozen=True)
class SparseTensorDirection:
    """A factored sparse binary vector; its support is never eagerly expanded."""

    factors: tuple[SparseBinaryVector, ...]

    def __post_init__(self) -> None:
        factors = tuple(self.factors)
        if any(not isinstance(factor, SparseBinaryVector) for factor in factors):
            raise ValueError("tensor factors must be SparseBinaryVector instances")
        object.__setattr__(self, "factors", factors)

    @property
    def dimension(self) -> int:
        return prod(factor.dimension for factor in self.factors)

    @property
    def dimensions(self) -> tuple[int, ...]:
        return tuple(factor.dimension for factor in self.factors)

    @property
    def weight(self) -> int:
        return prod(factor.weight for factor in self.factors)

    @property
    def norm(self) -> int:
        return prod(factor.norm for factor in self.factors)

    @property
    def weight_mod4(self) -> int:
        return prod(factor.weight_mod4 for factor in self.factors) & 3

    def iter_ones(self) -> Iterator[int]:
        for indices in product(*(factor.ones for factor in self.factors)):
            flat = 0
            for index, factor in zip(indices, self.factors):
                flat = flat * factor.dimension + index
            yield flat

    def contains(self, flat_index: int) -> bool:
        _integer(flat_index, "coordinate")
        if flat_index >= self.dimension:
            raise ValueError("coordinate outside tensor dimension")
        remainder = flat_index
        for factor in reversed(self.factors):
            remainder, index = divmod(remainder, factor.dimension)
            if not factor.contains(index):
                return False
        return True

    def same_shape(self, dimensions: Sequence[int]) -> bool:
        return self.dimensions == tuple(dimensions)

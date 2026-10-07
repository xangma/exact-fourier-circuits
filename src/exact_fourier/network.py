"""Constructive finite tensor network, with lazy syntax and exact budgets.

The scalar network is executable at small h and restores arbitrary auxiliary
data.  The saving seed is astronomically wide: never turn its factored counts
into ordinary integers or allocate its arrays.  A SeedPlan is a costed symbolic
program, not a Lean-verified WordStep list.
"""

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, product
from math import comb
from typing import Iterator, Sequence

from .gf2 import (SparseBinaryVector, SparseTensorDirection, full_coordinate_basis,
                  orthonormal_basis_complement)


def _integer(value, name, minimum=0):
    if isinstance(value, bool) or not isinstance(value, int) or value < minimum:
        raise ValueError(f"{name} must be an integer >= {minimum}")
    return value


def _combination_at(n: int, k: int, rank: int) -> tuple[int, ...]:
    if not 0 <= rank < comb(n, k):
        raise IndexError(rank)
    result = []
    start = 0
    for remaining in range(k, 0, -1):
        for value in range(start, n):
            count = comb(n - value - 1, remaining - 1)
            if rank < count:
                result.append(value)
                start = value + 1
                break
            rank -= count
    return tuple(result)


def _combination_rank(n: int, values: Sequence[int]) -> int:
    if tuple(values) != tuple(sorted(set(values))) or any(v < 0 or v >= n for v in values):
        raise ValueError("invalid combination")
    rank = 0
    start = 0
    for index, value in enumerate(values):
        remaining = len(values) - index - 1
        rank += sum(comb(n - candidate - 1, remaining) for candidate in range(start, value))
        start = value + 1
    return rank


@dataclass(frozen=True)
class NetworkParameters:
    h: int = 100

    def __post_init__(self):
        _integer(self.h, "h", 3)

    @property
    def v(self):
        return comb(self.h, 3)

    @property
    def degree(self):
        return comb(self.h - 3, 3) + 3 * (self.h - 3)

    @property
    def m(self):
        return self.h ** 3

    @property
    def bank_size(self):
        return self.v ** 3

    @property
    def invocations(self):
        return 3 * self.v ** 2

    @property
    def auxiliaries_per_invocation(self):
        return self.v * self.degree + self.h + 1

    @property
    def wires(self):
        return 2 * self.bank_size + self.invocations * self.auxiliaries_per_invocation

    @property
    def delta(self):
        return 2 * self.bank_size - 2 * self.invocations * (self.h + 1) * self.h

    @property
    def residual_dimensions(self):
        return self.wires * self.m - self.delta

    @property
    def scalar_shears(self):
        return self.invocations * (4 * self.v * self.degree + 16 * self.v)

    @property
    def pointwise_calls(self):
        # Every coefficient here is known nonzero; use three, not six, C calls.
        return 3 * self.scalar_shears

    def triple(self, index: int) -> tuple[int, ...]:
        return _combination_at(self.h, 3, index)

    def triple_index(self, triple: Sequence[int]) -> int:
        if len(triple) != 3:
            raise ValueError("a triple has three entries")
        return _combination_rank(self.h, triple)

    def neighbors(self, index: int) -> Iterator[int]:
        triple = self.triple(index)
        outside = tuple(value for value in range(self.h) if value not in triple)
        for neighbor in combinations(outside, 3):
            yield self.triple_index(neighbor)
        for pair in combinations(triple, 2):
            for value in outside:
                yield self.triple_index(tuple(sorted((*pair, value))))

    def neighbor_index(self, index: int, neighbor: int) -> int:
        triple = self.triple(index)
        other = self.triple(neighbor)
        shared = tuple(value for value in other if value in triple)
        outside = tuple(value for value in range(self.h) if value not in triple)
        if len(shared) == 0:
            return _combination_rank(len(outside), tuple(outside.index(value) for value in other))
        if len(shared) == 2:
            pair = tuple(combinations(triple, 2)).index(shared)
            value = next(value for value in other if value not in triple)
            return comb(self.h - 3, 3) + pair * len(outside) + outside.index(value)
        raise ValueError("triples must be distinct with even intersection")

    def bank_role(self, bank: str, indices: Sequence[int]) -> int:
        if bank not in ("X", "Y") or len(indices) != 3 or any(not 0 <= i < self.v for i in indices):
            raise ValueError("invalid bank role")
        return (bank == "Y") * self.bank_size + (indices[0] * self.v + indices[1]) * self.v + indices[2]

    def invocation(self, stage: int, fixed: tuple[int, int]):
        return Invocation(self, stage, fixed)

    def iter_invocations(self):
        for stage in range(3):
            for fixed in product(range(self.v), repeat=2):
                yield self.invocation(stage, fixed)


@dataclass(frozen=True)
class Shear:
    target: int
    source: int
    coefficient: Fraction


@dataclass(frozen=True)
class Invocation:
    parameters: NetworkParameters
    stage: int
    fixed: tuple[int, int]

    def __post_init__(self):
        if self.stage not in range(3) or len(self.fixed) != 2 or any(not 0 <= i < self.parameters.v for i in self.fixed):
            raise ValueError("invalid invocation")

    @property
    def inverse(self):
        return self.stage == 1

    @property
    def auxiliary_start(self):
        p = self.parameters
        number = self.stage * p.v ** 2 + self.fixed[0] * p.v + self.fixed[1]
        return 2 * p.bank_size + number * p.auxiliaries_per_invocation

    def indices(self, entry):
        result = list(self.fixed)
        result.insert(self.stage, entry)
        return tuple(result)

    def bank(self, physical_bank, entry):
        return self.parameters.bank_role(physical_bank, self.indices(entry))

    def side(self, physical_y, physical_x):
        p = self.parameters
        return self.auxiliary_start + physical_y * p.degree + p.neighbor_index(physical_y, physical_x)

    def center(self, index):
        if not 0 <= index <= self.parameters.h:
            raise IndexError(index)
        return self.auxiliary_start + self.parameters.v * self.parameters.degree + index

    def row_entries(self, row):
        if row not in range(8):
            raise IndexError(row)
        return range(self.parameters.v) if row in (0, 2, 5, 7) else (None,)

    def gate_shears(self, row: int, entry: int | None = None) -> Iterator[Shear]:
        """One physical gate; stage two reverses all eight updates and signs."""
        p = self.parameters
        forward_row = 7 - row if self.inverse else row
        sign = -1 if self.inverse else 1
        x_bank, y_bank = ("Y", "X") if self.inverse else ("X", "Y")

        def side(target, source):
            return self.side(source, target) if self.inverse else self.side(target, source)

        def emit(target, source, coefficient):
            return Shear(target, source, sign * Fraction(coefficient))

        if forward_row in (0, 5):
            if entry is None:
                raise ValueError("entry-specific gate")
            target = entry
            t = p.triple(target)
            for source in p.neighbors(target):
                intersection = len(set(t).intersection(p.triple(source)))
                coefficient = Fraction(intersection - 1, 2)
                if forward_row == 5:
                    coefficient = -coefficient
                yield emit(self.bank(y_bank, target), side(target, source), coefficient)
        elif forward_row in (2, 7):
            if entry is None:
                raise ValueError("entry-specific gate")
            source = entry
            for target in p.neighbors(source):
                yield emit(side(target, source), self.bank(x_bank, source), 1 if forward_row == 2 else -1)
        elif forward_row in (1, 4):
            for target in range(p.v):
                coefficient = Fraction(-1 if forward_row == 1 else 1, 2)
                for center in p.triple(target):
                    yield emit(self.bank(y_bank, target), self.center(center), coefficient)
                yield emit(self.bank(y_bank, target), self.center(p.h), -coefficient)
        else:
            for source in range(p.v):
                coefficient = 1 if forward_row == 3 else -1
                for center in p.triple(source):
                    yield emit(self.center(center), self.bank(x_bank, source), coefficient)
                yield emit(self.center(p.h), self.bank(x_bank, source), coefficient)

    def shears(self):
        for row in range(8):
            for entry in self.row_entries(row):
                yield from self.gate_shears(row, entry)


def iter_scalar_shears(parameters: NetworkParameters):
    for invocation in parameters.iter_invocations():
        yield from invocation.shears()


def apply_scalar_network(values: Sequence, parameters: NetworkParameters):
    """Return a new vector; accepts Fraction or compatible exact scalar types."""
    if len(values) != parameters.wires:
        raise ValueError(f"expected {parameters.wires} physical wires")
    result = list(values)
    for shear in iter_scalar_shears(parameters):
        result[shear.target] += shear.coefficient * result[shear.source]
    return result


def orthonormal_complement(length: int, lines: Sequence[SparseBinaryVector]):
    if any(v.dimension != length for v in lines):
        raise ValueError("different ambient spaces")
    yield from orthonormal_basis_complement(lines)


def _units(length):
    yield from full_coordinate_basis(length)


def _triple_line(parameters, entry):
    return SparseBinaryVector(parameters.h, parameters.triple(entry))


def _tensor_line(parameters, entries):
    factors = tuple(_triple_line(parameters, entry) for entry in entries)
    direction = SparseTensorDirection(factors)
    return SparseBinaryVector(direction.dimension, tuple(direction.iter_ones()))


def _tensor_bases(*factories):
    # Recursive lazy product: itertools.product eagerly materializes each input.
    def visit(index, factors):
        if index == len(factories):
            yield SparseTensorDirection(tuple(factors))
        else:
            for value in factories[index]():
                yield from visit(index + 1, (*factors, value))
    yield from visit(0, ())


@dataclass(frozen=True)
class Residual:
    kind: str
    x_entry: int | None = None
    y_entry: int | None = None

    def dimension(self, invocation):
        p = invocation.parameters
        E = p.h ** invocation.stage
        dimensions = {"B_t": E - 1, "B_tperp": (E - 1) * (p.h - 1), "B_D": (E - 1) * p.h,
                      "P_tperp": p.h - 1, "P_D": p.h, "P_t": 1,
                      "side_0_2": (E - 1) * (p.h - 1) + 1, "P_pairperp": p.h - 2,
                      "terminal_aux": E * p.h * (p.h ** (2 - invocation.stage) - 1)}
        return dimensions[self.kind]

    def basis(self, invocation):
        p = invocation.parameters
        prefix = _tensor_line(p, invocation.fixed[:invocation.stage])
        future = _tensor_line(p, invocation.fixed[invocation.stage:])
        P = lambda: iter((prefix,))
        B = lambda: orthonormal_complement(prefix.dimension, (prefix,))
        E = lambda: _units(prefix.dimension)
        Q = lambda: iter((future,))
        D = lambda: _units(p.h)
        X = lambda: iter((_triple_line(p, self.x_entry),))
        Y = lambda: iter((_triple_line(p, self.y_entry),))
        Xperp = lambda: orthonormal_complement(p.h, (_triple_line(p, self.x_entry),))
        Yperp = lambda: orthonormal_complement(p.h, (_triple_line(p, self.y_entry),))
        if self.kind == "B_t":
            yield from _tensor_bases(B, Y, Q)
        elif self.kind == "B_tperp":
            yield from _tensor_bases(B, Xperp if self.x_entry is not None else Yperp, Q)
        elif self.kind == "B_D":
            yield from _tensor_bases(B, D, Q)
        elif self.kind == "P_tperp":
            yield from _tensor_bases(P, Xperp if self.x_entry is not None else Yperp, Q)
        elif self.kind == "P_D":
            yield from _tensor_bases(P, D, Q)
        elif self.kind == "P_t":
            yield from _tensor_bases(P, Y if self.y_entry is not None else X, Q)
        elif self.kind == "side_0_2":
            yield from _tensor_bases(B, Yperp, Q)
            yield from _tensor_bases(P, X, Q)
        elif self.kind == "P_pairperp":
            pairperp = lambda: orthonormal_complement(p.h, (_triple_line(p, self.x_entry), _triple_line(p, self.y_entry)))
            yield from _tensor_bases(P, pairperp, Q)
        elif self.kind == "terminal_aux":
            Qperp = lambda: orthonormal_complement(future.dimension, (future,))
            yield from _tensor_bases(E, D, Qperp)
        else:
            raise ValueError(self.kind)


def _gate_edges(invocation, row, entry):
    """(physical role, residual descriptor, increasing) before one scalar gate."""
    p = invocation.parameters
    if row == 0:
        for x in p.neighbors(entry):
            yield invocation.side(entry, x), Residual("B_t", y_entry=entry), True
    elif row == 1:
        for y in range(p.v):
            yield invocation.bank("Y", y), Residual("B_tperp", y_entry=y), True
        for center in range(p.h + 1):
            yield invocation.center(center), Residual("B_D"), True
    elif row == 2:
        yield invocation.bank("X", entry), Residual("B_tperp", x_entry=entry), True
        for y in p.neighbors(entry):
            yield invocation.side(y, entry), Residual("side_0_2", x_entry=entry, y_entry=y), True
    elif row == 3:
        for x in range(p.v):
            yield invocation.bank("X", x), Residual("P_tperp", x_entry=x), True
        for center in range(p.h + 1):
            yield invocation.center(center), Residual("P_D"), True
    elif row == 4:
        for center in range(p.h + 1):
            yield invocation.center(center), Residual("P_D"), False
    elif row == 5:
        yield invocation.bank("Y", entry), Residual("P_tperp", y_entry=entry), True
        for x in p.neighbors(entry):
            yield invocation.side(entry, x), Residual("P_pairperp", x_entry=x, y_entry=entry), True
    elif row == 6:
        for center in range(p.h + 1):
            yield invocation.center(center), Residual("P_D"), True
    elif row == 7:
        for y in p.neighbors(entry):
            yield invocation.side(y, entry), Residual("P_t", y_entry=y), True


@dataclass(frozen=True)
class DirectionalStep:
    role: int
    direction: SparseTensorDirection
    columns: int
    inverse: bool

    @property
    def description(self):
        return "C_z in every column; inverse additionally translates by z"


@dataclass(frozen=True)
class PointwiseShear:
    shear: Shear
    address_bits: int


@dataclass(frozen=True)
class TerminalCorrection:
    parameters: NetworkParameters
    columns: int

    def exceptional_translations(self):
        p = self.parameters
        for entries in product(range(p.v), repeat=3):
            yield p.bank_role("Y", entries), _tensor_line(p, entries), self.columns

    def signed_bank_pairs(self):
        # New X = old Y; new Y = -old X, after correcting translations on Y.
        p = self.parameters
        for index in range(p.bank_size):
            yield index, p.bank_size + index


@dataclass(frozen=True)
class PaddedRoles:
    start: int
    stop: int
    bits_per_column: int
    columns: int


@dataclass(frozen=True)
class RoleAxes:
    role_bits: int
    address_bits: int


def iter_network_program(parameters: NetworkParameters, columns: int = 1):
    """Generate the framed network lazily, using only existing physical roles.

    Instructions are structured operations, not a flat list of C calls.  Each
    DirectionalStep expands to columns * 2^(m*columns-1) forward calls, plus
    a permutation for an inverse.  PointwiseShear expands using three calls
    per address.  TerminalCorrection is a monomial, with no C calls.
    """
    _integer(columns, "columns", 1)
    for invocation in parameters.iter_invocations():
        for row in range(8):
            for entry in invocation.row_entries(row):
                for role, residual, increasing in _gate_edges(invocation, row, entry):
                    if residual.dimension(invocation) == 0:
                        continue
                    for direction in residual.basis(invocation):
                        inverse = (direction.weight_mod4 == 3) == increasing
                        yield DirectionalStep(role, direction, columns, inverse)
                for shear in invocation.gate_shears(row, entry):
                    yield PointwiseShear(shear, parameters.m * columns)
        residual = Residual("terminal_aux")
        for role in range(invocation.auxiliary_start, invocation.auxiliary_start + parameters.auxiliaries_per_invocation):
            for direction in residual.basis(invocation):
                yield DirectionalStep(role, direction, columns, direction.weight_mod4 == 3)
    yield TerminalCorrection(parameters, columns)


def apply_network_walsh_mode(values, parameters, frequency_columns, max_symbolic_steps=1_000_000):
    """Exact framed-network evaluation on one Walsh mode of every physical role.

    Each array is amplitude * (-1)^(frequency dot address).  This subspace is
    preserved by every instruction, so amplitudes alone suffice for exact
    execution.  This tests the complete framed operator on that subspace;
    it does not execute a general array of length 2^(m*columns).
    """
    from .scalars import GaussianRational
    frequencies = tuple(frequency_columns)
    if not frequencies:
        raise ValueError("at least one frequency column is required")
    for frequency in frequencies:
        _integer(frequency, "frequency")
        if frequency.bit_length() > parameters.m:
            raise ValueError("frequency is outside one address column")
    if parameters.residual_dimensions + parameters.scalar_shears > max_symbolic_steps:
        raise ValueError("symbolic network exceeds the bounded evaluator; use the lazy program")
    if len(values) != parameters.wires:
        raise ValueError(f"expected {parameters.wires} amplitudes")
    amplitudes = [GaussianRational.coerce(value) for value in values]
    phases = (GaussianRational(1), GaussianRational(0, 1), GaussianRational(-1), GaussianRational(0, -1))

    def parity(direction, frequency):
        return sum((frequency >> position) & 1 for position in direction.iter_ones()) % 2

    for instruction in iter_network_program(parameters, len(frequencies)):
        if isinstance(instruction, DirectionalStep):
            exponent = sum(parity(instruction.direction, frequency) for frequency in frequencies)
            if instruction.inverse:
                exponent = -exponent
            amplitudes[instruction.role] *= phases[exponent % 4]
        elif isinstance(instruction, PointwiseShear):
            shear = instruction.shear
            amplitudes[shear.target] += shear.coefficient * amplitudes[shear.source]
        else:
            for role, direction, _ in instruction.exceptional_translations():
                if sum(parity(direction, frequency) for frequency in frequencies) % 2:
                    amplitudes[role] = -amplitudes[role]
            for x, y in instruction.signed_bank_pairs():
                amplitudes[x], amplitudes[y] = amplitudes[y], -amplitudes[x]
    return amplitudes


@dataclass(frozen=True)
class FactoredCount:
    coefficient: int
    exponent: int

    def __post_init__(self):
        _integer(self.coefficient, "coefficient")
        _integer(self.exponent, "exponent")

    def __str__(self):
        return f"{self.coefficient} * 2^{self.exponent}"

    def to_int(self, max_bits=4096):
        if self.coefficient.bit_length() + self.exponent > max_bits:
            raise ValueError("count intentionally retained in factored form")
        return self.coefficient << self.exponent


@dataclass(frozen=True)
class SeedPlan:
    parameters: NetworkParameters
    f: int
    role_bits: int
    padded_roles: int
    directional_steps: int
    H: int
    b: int
    calls: FactoredCount
    ordinary_calls: FactoredCount
    saved_calls: FactoredCount
    expanded: bool = False
    kernel_verified: bool = False

    def instructions(self):
        """Global index=(role << (m*f))|address; column c uses bits c*m..(c+1)*m-1.

        Padding applies ordinary C layers to all address bits of added roles;
        role axis j applies the C pair layer at global bit m*f+j.
        """
        yield from iter_network_program(self.parameters, self.f)
        yield PaddedRoles(self.parameters.wires, self.padded_roles, self.parameters.m, self.f)
        yield RoleAxes(self.role_bits, self.parameters.m * self.f)

    def metadata(self):
        p = self.parameters
        return {"h": p.h, "v": p.v, "neighbors": p.degree, "m": p.m, "W": p.wires,
                "W_star": self.padded_roles, "role_bits": self.role_bits, "Delta": p.delta,
                "S": self.directional_steps, "scalar_shears": p.scalar_shears,
                "H": self.H, "f": self.f, "b": self.b, "width": f"2^{self.b}",
                "calls": str(self.calls), "ordinary_calls": str(self.ordinary_calls),
                "saved_calls": str(self.saved_calls), "expanded": self.expanded,
                "kernel_verified": self.kernel_verified,
                "status": "lazy constructive program and arithmetic budget; no full execution or formal witness verification"}


def saving_seed_plan(h=100, f=None):
    p = NetworkParameters(h)
    if p.delta <= 0:
        raise ValueError("this network has no positive dimension saving; h >= 22 required")
    H = p.pointwise_calls
    minimum_f = 2 * H // p.delta + 1
    if f is None:
        f = minimum_f
    _integer(f, "f", 1)
    if f < minimum_f:
        raise ValueError(f"three-call shear compilation requires f >= {minimum_f}")
    role_bits = (p.wires - 1).bit_length()
    padded = 1 << role_bits  # Only <=71 bits for the paper parameters.
    S = padded * p.m - p.delta
    b = p.m * f + role_bits
    exponent = p.m * f - 1
    calls = FactoredCount(S * f + role_bits * padded + 2 * H, exponent)
    ordinary = FactoredCount(b * padded, exponent)
    saved = FactoredCount(p.delta * f - 2 * H, exponent)
    assert calls.coefficient + saved.coefficient == ordinary.coefficient
    assert saved.coefficient > 0
    return SeedPlan(p, f, role_bits, padded, S, H, b, calls, ordinary, saved)

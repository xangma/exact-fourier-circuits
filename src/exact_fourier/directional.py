"""Bounded executable expansion of the network's directional operations.

For a binary direction z, C_z = A*identity + B*translation_by_z. A call acts
on each address pair {x, x xor z}. Inverse C_z is translation_by_z followed
by forward C_z, because C_z^2 is translation_by_z.

Direction support index j names address bit j (least significant bit first).
Column c occupies the m-bit block starting at c*m. Support indices within a
direction use SparseTensorDirection's row-major tensor flattening. A returned
Word acts on one role's address array; the role label is not part of its width.
"""

from __future__ import annotations

from typing import Any, Sequence

from .gf2 import SparseTensorDirection
from .network import DirectionalStep
from .scalars import GaussianRational as QI
from .words import A, B, Call, KERNEL_C, Permute, Word


def _integer(value: Any, name: str, minimum: int = 0) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < minimum:
        raise ValueError(f"{name} must be an integer at least {minimum}")
    return value


def _layout(direction: SparseTensorDirection, columns: int, *, max_inputs: int,
            max_address_bits: int, max_calls: int) -> tuple[int, tuple[int, ...], int]:
    if not isinstance(direction, SparseTensorDirection):
        raise ValueError("direction must be a SparseTensorDirection")
    columns = _integer(columns, "columns", 1)
    max_inputs = _integer(max_inputs, "max_inputs", 2)
    max_address_bits = _integer(max_address_bits, "max_address_bits", 1)
    max_calls = _integer(max_calls, "max_calls")
    m = direction.dimension
    bits = m * columns
    # Check both limits before creating a bitmask or an address-space integer.
    if bits > max_address_bits or bits >= max_inputs.bit_length():
        raise ValueError("directional address space exceeds the materialization input/bit limit")
    if m < 1 or direction.norm != 1:
        raise ValueError("direction must have positive dimension and norm one")
    width = 1 << bits
    if width > max_inputs:
        raise ValueError("directional address space exceeds the materialization input limit")
    calls = columns * (width // 2)
    if calls > max_calls:
        raise ValueError("directional calls exceed materialization call limit")
    mask = sum(1 << index for index in direction.iter_ones())
    masks = tuple(mask << (column * m) for column in range(columns))
    return width, masks, m


def directional_word(direction: SparseTensorDirection, columns: int = 1, inverse: bool = False, *,
                     max_inputs: int = 256, max_address_bits: int = 16,
                     max_calls: int = 250_000) -> Word:
    """Expand one C_z per column into forward C calls and a free permutation.

    The bit and input caps are checked before shifts; the call cap is checked
    before constructing the list. No astronomical SeedPlan is expanded here.
    """
    if type(inverse) is not bool:
        raise ValueError("inverse must be a bool")
    width, masks, _ = _layout(direction, columns, max_inputs=max_inputs,
                              max_address_bits=max_address_bits, max_calls=max_calls)
    steps = []
    for mask in masks:
        pivot = mask & -mask
        for address in range(width):
            if address & pivot == 0:
                steps.append(Call((address, address ^ mask)))
    if inverse:
        translation = 0
        for mask in masks:
            translation ^= mask
        steps.append(Permute(tuple(address ^ translation for address in range(width))))
    return Word(KERNEL_C, width, tuple(steps))


def expand_directional_step(step: DirectionalStep, **limits: Any) -> Word:
    """Expand the isolated address array of a network DirectionalStep."""
    if not isinstance(step, DirectionalStep):
        raise ValueError("expected a DirectionalStep")
    _integer(step.role, "role")
    return directional_word(step.direction, step.columns, step.inverse, **limits)


def apply_directional_exact(values: Sequence[Any], direction: SparseTensorDirection,
                            columns: int = 1, inverse: bool = False, *,
                            max_inputs: int = 256, max_address_bits: int = 16,
                            max_calls: int = 250_000) -> tuple[QI, ...]:
    """Apply the direct formula, useful for a bounded independent comparison."""
    if type(inverse) is not bool:
        raise ValueError("inverse must be a bool")
    width, masks, _ = _layout(direction, columns, max_inputs=max_inputs,
                              max_address_bits=max_address_bits, max_calls=max_calls)
    if len(values) != width:
        raise ValueError(f"expected {width} address values, got {len(values)}")
    result = tuple(QI.coerce(value) for value in values)
    a, b = (B, A) if inverse else (A, B)
    for mask in masks:
        result = tuple(a * result[address] + b * result[address ^ mask] for address in range(width))
    return result

"""Exact finite quotients of the framed network's enormous address space.

A surjective binary map L identifies functions g(Lx).  On this invariant
subspace, translation by z becomes translation by Lz.  The resulting program
is an executable algebraic quotient, not the original saving word.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from random import Random
from typing import Iterable, Sequence

from .gf2 import SparseBinaryVector, SparseTensorDirection
from .network import (DirectionalStep, NetworkParameters, PointwiseShear,
                      TerminalCorrection, iter_network_program)
from .scalars import GaussianRational as QI
from .words import A, B, Call, Scale, shear_steps


def _integer(value, name, minimum=0):
    if isinstance(value, bool) or not isinstance(value, int) or value < minimum:
        raise ValueError(f"{name} must be an integer >= {minimum}")
    return value


def _binary_rank(vectors):
    pivots = {}
    for vector in vectors:
        while vector:
            pivot = vector.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = vector
                break
            vector ^= pivots[pivot]
    return len(pivots)


@dataclass(frozen=True)
class BinaryProjection:
    """Column j of L is the k-bit integer images[j]; address bits are LSB first."""

    images: tuple[int, ...]
    address_bits: int

    def __post_init__(self):
        _integer(self.address_bits, "address_bits")
        images = tuple(self.images)
        if not images or self.address_bits > len(images):
            raise ValueError("projection dimension must not exceed nonempty ambient dimension")
        for image in images:
            _integer(image, "basis image")
            if image.bit_length() > self.address_bits:
                raise ValueError("basis image exceeds the projected address dimension")
        if _binary_rank(images) != self.address_bits:
            raise ValueError("binary projection must be surjective")
        object.__setattr__(self, "images", images)

    @property
    def ambient_bits(self):
        return len(self.images)

    def project(self, vector: int):
        _integer(vector, "ambient vector")
        if vector.bit_length() > self.ambient_bits:
            raise ValueError("vector exceeds ambient dimension")
        result = 0
        while vector:
            bit = vector & -vector
            result ^= self.images[bit.bit_length() - 1]
            vector ^= bit
        return result

    def direction_mask(self, direction: SparseBinaryVector | SparseTensorDirection, column=0):
        _integer(column, "column")
        offset = column * direction.dimension
        if offset + direction.dimension > self.ambient_bits:
            raise ValueError("direction column exceeds projection domain")
        result = 0
        for position in direction.iter_ones():
            result ^= self.images[offset + position]
        return result

    def pullback(self, values, *, max_ambient_bits=16):
        """Bounded explicit g(Lx), used only for small intertwining tests."""
        if self.ambient_bits > max_ambient_bits:
            raise ValueError("pullback exceeds ambient materialization limit")
        if len(values) != 1 << self.address_bits:
            raise ValueError("wrong reduced address width")
        return tuple(values[self.project(address)] for address in range(1 << self.ambient_bits))

    def to_dict(self):
        return {"address_bits": self.address_bits, "ambient_bits": self.ambient_bits,
                "images": list(self.images)}


def random_projection(ambient_bits, address_bits, seed=130):
    _integer(ambient_bits, "ambient_bits", 1)
    _integer(address_bits, "address_bits")
    _integer(seed, "seed")
    if address_bits > ambient_bits:
        raise ValueError("projection dimension exceeds ambient dimension")
    random = Random(seed)
    # An explicit identity minor proves surjectivity; the remaining columns
    # spread directions across the smaller address space reproducibly.
    images = tuple(1 << bit for bit in range(address_bits)) + tuple(
        random.getrandbits(address_bits) for _ in range(ambient_bits - address_bits))
    return BinaryProjection(images, address_bits)


@dataclass(frozen=True)
class Checkpoint:
    label: str
    record_index: int

    def to_dict(self):
        return {"label": self.label, "record_index": self.record_index}


# Record fields: op, target, arg, coefficient numerator, denominator, inverse.
# 0: C_arg on target role (possibly inverse); 1: target += (num/den)*arg role;
# 2: signed bank pair X=target,Y=arg; 3: translate target by arg;
# 4: C along a role-index bit arg, target unused.  Zero masks are retained.
Record = tuple[int, int, int, int, int, bool]


@dataclass(frozen=True)
class ProjectedProgram:
    projection: BinaryProjection
    records: tuple[Record, ...]
    checkpoints: tuple[Checkpoint, ...]
    metadata: dict

    def to_dict(self):
        return {"schema": "exact-fourier-projected-program/v1",
                "projection": self.projection.to_dict(), "metadata": dict(self.metadata),
                "records": [list(record) for record in self.records],
                "checkpoints": [checkpoint.to_dict() for checkpoint in self.checkpoints]}


def build_projected_program(h=4, bits=6, columns=1, seed=130, include_padding=True, *,
                            max_records=250_000, max_state_entries=1_048_576):
    """Project every original network instruction; preserve algebraic identities.

    Each original directional macro produces one C_Lz record per column.
    Padding supplies the ordinary coordinate directions, and the final layers
    transform the role-index bits.  Full coordinates use role as the high
    field and reduced address as the low field.
    """
    p = NetworkParameters(h)
    _integer(bits, "bits")
    _integer(columns, "columns", 1)
    _integer(max_records, "max_records", 1)
    _integer(max_state_entries, "max_state_entries", 1)
    if type(include_padding) is not bool:
        raise ValueError("include_padding must be bool")
    if bits > p.m * columns or bits >= max_state_entries.bit_length():
        raise ValueError("projected dimension exceeds state limit")
    role_bits = (p.wires - 1).bit_length() if include_padding else 0
    roles = (1 << role_bits) if include_padding else p.wires
    width = 1 << bits
    if roles * width > max_state_entries:
        raise ValueError("projected role/address state exceeds materialization limit")
    expected = columns * p.residual_dimensions + p.scalar_shears + 2 * p.bank_size
    if include_padding:
        expected += (roles - p.wires) * p.m * columns + role_bits
    if expected > max_records:
        raise ValueError("projected instruction count exceeds materialization limit")
    projection = random_projection(p.m * columns, bits, seed)
    records = []
    checkpoints = []
    stage = 0

    def append(op, target=0, arg=0, numerator=0, denominator=1, inverse=False):
        records.append((op, target, arg, numerator, denominator, inverse))

    def checkpoint(label):
        checkpoints.append(Checkpoint(label, len(records)))

    def auxiliary_stage(instruction):
        role = instruction.role if isinstance(instruction, DirectionalStep) else max(instruction.shear.target, instruction.shear.source)
        if role < 2 * p.bank_size:
            return None
        invocation_index = (role - 2 * p.bank_size) // p.auxiliaries_per_invocation
        return invocation_index // (p.v * p.v)

    for instruction in iter_network_program(p, columns):
        if isinstance(instruction, TerminalCorrection):
            checkpoint("stage_3")
            for role, direction, _ in instruction.exceptional_translations():
                mask = 0
                for column in range(columns):
                    mask ^= projection.direction_mask(direction, column)
                append(3, role, mask)
            checkpoint("terminal_translation")
            for x, y in instruction.signed_bank_pairs():
                append(2, x, y)
            checkpoint("terminal_bank_exchange")
            continue
        next_stage = auxiliary_stage(instruction)
        if next_stage is not None and next_stage > stage:
            checkpoint(f"stage_{stage + 1}")
            stage = next_stage
        if isinstance(instruction, DirectionalStep):
            for column in range(columns):
                append(0, instruction.role, projection.direction_mask(instruction.direction, column), inverse=instruction.inverse)
        else:
            shear = instruction.shear
            append(1, shear.target, shear.source, shear.coefficient.numerator, shear.coefficient.denominator)
    if include_padding:
        for role in range(p.wires, roles):
            for image in projection.images:
                append(0, role, image)
        checkpoint("padding")
        for bit in range(role_bits):
            append(4, arg=1 << bit)
        checkpoint("role_axes")
    if len(records) != expected:
        raise AssertionError("projected instruction count differs from independent budget")
    if tuple(c.label for c in checkpoints[:3]) != ("stage_1", "stage_2", "stage_3"):
        raise AssertionError("network stage boundaries were not recovered")
    metadata = {"h": h, "m": p.m, "columns": columns, "seed": seed,
                "address_bits": bits, "ambient_bits": p.m * columns,
                "width": width, "roles": roles, "original_roles": p.wires,
                "bank_size": p.bank_size, "role_bits": role_bits,
                "include_padding": include_padding,
                "original_directional_steps": p.residual_dimensions,
                "original_pointwise_shears": p.scalar_shears,
                "record_count": len(records),
                "zero_direction_records": sum(op == 0 and arg == 0 for op, _, arg, _, _, _ in records),
                "status": "exact algebraic projection; no saving or full-word verification claim",
                "coordinate_layout": "(role << address_bits) | reduced_address; column c starts at original bit c*m"}
    return ProjectedProgram(projection, tuple(records), tuple(checkpoints), metadata)


def _values(program, values):
    roles, width = program.metadata["roles"], program.metadata["width"]
    if len(values) != roles or any(len(row) != width for row in values):
        raise ValueError(f"expected amplitudes shaped ({roles},{width})")
    return [[QI.coerce(value) for value in row] for row in values]


def _c_pair(u, v):
    # Same four scalar operations used by Word.compile; exact in Q(i).
    t = B * (v - u)
    return u + t, v - t


def _directional(row, mask, inverse=False):
    if mask == 0:
        return
    pivot = mask & -mask
    for address in range(len(row)):
        if not address & pivot:
            other = address ^ mask
            u, v = _c_pair(row[address], row[other])
            row[address], row[other] = (v, u) if inverse else (u, v)


@lru_cache(maxsize=16)
def _compiled_shear(numerator, denominator):
    return shear_steps(0, 1, Fraction(numerator, denominator))


def _shear(target, source, numerator, denominator, compiled):
    if not compiled:
        coefficient = QI(Fraction(numerator, denominator))
        for address in range(len(target)):
            target[address] += coefficient * source[address]
        return
    for step in _compiled_shear(numerator, denominator):
        if isinstance(step, Scale):
            row = target if step.coordinate == 0 else source
            for address in range(len(row)):
                row[address] *= step.coefficient
        elif isinstance(step, Call):
            for address in range(len(target)):
                target[address], source[address] = _c_pair(target[address], source[address])
        else:
            raise AssertionError("nonzero shear compiler unexpectedly emitted a permutation")


@dataclass(frozen=True)
class ExactProjectionRun:
    final: tuple[tuple[QI, ...], ...]
    checkpoints: tuple[tuple[str, tuple[tuple[QI, ...], ...]], ...]


def evaluate_projected_exact(program: ProjectedProgram, values, *, compiled_shears=True,
                             capture_checkpoints=False, max_scalar_cells=2_000_000):
    """Run every record with exact Gaussian rationals on bounded dirty arrays.

    Compiled shear mode executes all three C calls and all monomial scalings,
    temporarily mutating the source row and restoring it at the end.  Direct
    shear mode is an independent economical algebraic comparison.
    """
    if type(compiled_shears) is not bool or type(capture_checkpoints) is not bool:
        raise ValueError("evaluator modes must be bool")
    if len(program.records) * program.metadata["width"] > max_scalar_cells:
        raise ValueError("exact projected evaluation exceeds bounded operation limit")
    result = _values(program, values)
    checkpoints = []
    boundaries = {checkpoint.record_index: checkpoint.label for checkpoint in program.checkpoints}
    for index, (op, target, arg, numerator, denominator, inverse) in enumerate(program.records, 1):
        if op == 0:
            _directional(result[target], arg, inverse)
        elif op == 1:
            _shear(result[target], result[arg], numerator, denominator, compiled_shears)
        elif op == 2:
            result[target], result[arg] = result[arg], [-value for value in result[target]]
        elif op == 3:
            result[target] = [result[target][address ^ arg] for address in range(program.metadata["width"])]
        elif op == 4:
            for role in range(len(result)):
                if not role & arg:
                    other = role ^ arg
                    for address in range(program.metadata["width"]):
                        result[role][address], result[other][address] = _c_pair(result[role][address], result[other][address])
        else:
            raise ValueError(f"unknown projected operation {op}")
        if capture_checkpoints and index in boundaries:
            checkpoints.append((boundaries[index], tuple(tuple(row) for row in result)))
    return ExactProjectionRun(tuple(tuple(row) for row in result), tuple(checkpoints))


def _walsh(values):
    result = list(values)
    stride = 1
    while stride < len(result):
        for start in range(0, len(result), 2 * stride):
            for offset in range(stride):
                a, b = start + offset, start + offset + stride
                u, v = result[a], result[b]
                result[a], result[b] = u + v, u - v
        stride *= 2
    return result


def projected_target_exact(program: ProjectedProgram, values):
    """Independent target: Walsh spectrum of the projected original unit axes.

    Translation by image_j has Walsh eigenvalue (-1)^(image_j dot frequency),
    hence the tensor C target has eigenvalue i^(sum_j(image_j dot frequency)).
    The final role-bit transform is then applied by its literal two-by-two
    matrix, independently of the source directional and shear interpreters.
    """
    result = _values(program, values)
    width = program.metadata["width"]
    phases = (QI(1), QI(0, 1), QI(-1), QI(0, -1))
    spectrum = [phases[sum((image & frequency).bit_count() % 2 for image in program.projection.images) % 4]
                for frequency in range(width)]
    for role, row in enumerate(result):
        transformed = _walsh(row)
        transformed = [value * spectrum[frequency] for frequency, value in enumerate(transformed)]
        result[role] = [value / width for value in _walsh(transformed)]
    for bit in range(program.metadata["role_bits"]):
        mask = 1 << bit
        for role in range(len(result)):
            if not role & mask:
                other = role ^ mask
                for address in range(width):
                    u, v = result[role][address], result[other][address]
                    result[role][address], result[other][address] = A * u + B * v, B * u + A * v
    return tuple(tuple(row) for row in result)

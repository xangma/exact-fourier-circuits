"""Chronological exact scalar-gate circuits and bounded basis certificates.

References 0..n_inputs-1 name inputs; each gate appends one available value.
The reference -1 names literal zero. Output aliases and permutations are free.
Every emitted add, subtract, or constant multiplication costs one gate.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from typing import Any, Iterable, Sequence

from .scalars import GaussianRational as QI, ONE, ZERO as SCALAR_ZERO


ZERO = -1
SCHEMA = "exact-fourier-circuit/v1"
DEFAULT_MAX_VALUES = 1_000_000
DEFAULT_MAX_ENTRIES = 262_144
DEFAULT_MAX_WORK = 20_000_000


def _integer(value: Any, name: str, minimum: int | None = None) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError(f"{name} must be an integer")
    if minimum is not None and value < minimum:
        raise ValueError(f"{name} must be at least {minimum}")
    return value


def _reference(ref: Any, available: int, name: str) -> int:
    ref = _integer(ref, name)
    if ref != ZERO and not 0 <= ref < available:
        raise ValueError(f"{name} {ref} is unavailable; expected -1 or 0..{available - 1}")
    return ref


def _limit(size: int, maximum: int, name: str) -> None:
    _integer(maximum, f"max_{name}", 0)
    if size > maximum:
        raise ValueError(f"{name} {size} exceeds limit {maximum}")


@dataclass(frozen=True)
class Gate:
    op: str
    a: int
    b: int | None = None
    coefficient: QI | None = None

    def __post_init__(self) -> None:
        if self.op not in ("add", "sub", "scale"):
            raise ValueError(f"unsupported gate operation {self.op!r}")
        _integer(self.a, "gate operand a")
        if self.op == "scale":
            if self.b is not None or self.coefficient is None:
                raise ValueError("scale requires coefficient and exactly one operand")
            object.__setattr__(self, "coefficient", QI.coerce(self.coefficient))
        elif self.b is None or self.coefficient is not None:
            raise ValueError("add/sub require two operands and no coefficient")
        else:
            _integer(self.b, "gate operand b")

    def to_dict(self) -> dict[str, Any]:
        if self.op == "scale":
            return {"op": self.op, "a": self.a, "coefficient": self.coefficient.to_dict()}
        return {"op": self.op, "a": self.a, "b": self.b}

    @classmethod
    def from_dict(cls, value: Any) -> Gate:
        if not isinstance(value, dict):
            raise ValueError("gate must be an object")
        op = value.get("op")
        required = {"op", "a", "coefficient"} if op == "scale" else {"op", "a", "b"}
        if set(value) != required:
            raise ValueError("unexpected or missing gate fields")
        if op == "scale":
            return cls(op, value["a"], coefficient=QI.from_dict(value["coefficient"]))
        return cls(op, value["a"], value["b"])


@dataclass(frozen=True)
class Circuit:
    n_inputs: int
    gates: tuple[Gate, ...] = ()
    outputs: tuple[int, ...] = ()

    def __post_init__(self) -> None:
        _integer(self.n_inputs, "n_inputs", 0)
        object.__setattr__(self, "gates", tuple(self.gates))
        object.__setattr__(self, "outputs", tuple(self.outputs))
        for index, gate in enumerate(self.gates):
            if not isinstance(gate, Gate):
                raise ValueError("all gates must be Gate instances")
            available = self.n_inputs + index
            _reference(gate.a, available, f"gate {index} operand a")
            if gate.b is not None:
                _reference(gate.b, available, f"gate {index} operand b")
        for index, ref in enumerate(self.outputs):
            _reference(ref, self.n_values, f"output {index}")

    @property
    def gate_count(self) -> int:
        return len(self.gates)

    @property
    def n_outputs(self) -> int:
        return len(self.outputs)

    @property
    def n_values(self) -> int:
        return self.n_inputs + self.gate_count

    def operation_counts(self) -> dict[str, int]:
        return {op: sum(gate.op == op for gate in self.gates) for op in ("add", "sub", "scale")}

    def evaluate(self, inputs: Sequence[Any], *, max_values: int = DEFAULT_MAX_VALUES,
                 max_bits: int | None = None) -> tuple[QI, ...]:
        """Evaluate with exact arithmetic, retaining chronological available values."""
        if len(inputs) != self.n_inputs:
            raise ValueError(f"expected {self.n_inputs} inputs, got {len(inputs)}")
        _limit(self.n_values, max_values, "values")
        _limit(self.n_outputs, max_values, "outputs")
        if max_bits is not None:
            _integer(max_bits, "max_bits", 1)
        values = [QI.coerce(value) for value in inputs]

        def read(ref: int) -> QI:
            return SCALAR_ZERO if ref == ZERO else values[ref]

        def check(value: QI) -> None:
            if max_bits is not None and value.bit_length() > max_bits:
                raise ValueError(f"scalar bit length exceeds limit {max_bits}")

        for value in values:
            check(value)
        for gate in self.gates:
            a = read(gate.a)
            if gate.op == "scale":
                value = gate.coefficient * a
            elif gate.op == "add":
                value = a + read(gate.b)
            else:
                value = a - read(gate.b)
            check(value)
            values.append(value)
        return tuple(read(ref) for ref in self.outputs)

    def linear_matrix(self, *, max_entries: int = DEFAULT_MAX_ENTRIES,
                      max_work: int = DEFAULT_MAX_WORK,
                      max_values: int = DEFAULT_MAX_VALUES,
                      max_bits: int | None = None) -> tuple[tuple[QI, ...], ...]:
        """Return output-by-input coefficients; check every standard basis input.

        Linearity follows structurally: every allowed gate is linear, and no
        nonzero constant input exists. Exact basis agreement therefore covers
        every input over any field containing Q(i).
        """
        _limit(self.n_outputs * self.n_inputs, max_entries, "entries")
        _limit(self.n_inputs * self.n_values, max_work, "work")
        _limit(self.n_values, max_values, "values")
        rows = [[] for _ in self.outputs]
        for index in range(self.n_inputs):
            basis = [SCALAR_ZERO] * self.n_inputs
            basis[index] = ONE
            for row, value in zip(rows, self.evaluate(basis, max_values=max_values, max_bits=max_bits)):
                row.append(value)
        return tuple(tuple(row) for row in rows)

    def verify_matrix(self, expected: Sequence[Sequence[Any]], **limits: Any) -> bool:
        matrix = exact_matrix(expected, rows=self.n_outputs, columns=self.n_inputs,
                              max_entries=limits.get("max_entries", DEFAULT_MAX_ENTRIES))
        return self.linear_matrix(**limits) == matrix

    def linear_map_certificate(self, expected: Sequence[Sequence[Any]], **limits: Any) -> dict[str, Any]:
        """A reproducible exact basis certificate, not a Lean proof artifact."""
        matrix = exact_matrix(expected, rows=self.n_outputs, columns=self.n_inputs,
                              max_entries=limits.get("max_entries", DEFAULT_MAX_ENTRIES))
        actual = self.linear_matrix(**limits)
        return {"method": "exact-standard-basis-and-structural-linearity",
                "passed": actual == matrix, "circuit_sha256": self.stable_hash(),
                "expected_matrix_sha256": matrix_digest(matrix, max_entries=limits.get("max_entries", DEFAULT_MAX_ENTRIES)),
                "actual_matrix_sha256": matrix_digest(actual, max_entries=limits.get("max_entries", DEFAULT_MAX_ENTRIES)),
                "n_inputs": self.n_inputs, "n_outputs": self.n_outputs,
                "basis_inputs_checked": self.n_inputs,
                "entries_checked": self.n_inputs * self.n_outputs}

    def to_dict(self) -> dict[str, Any]:
        return {"schema": SCHEMA, "n_inputs": self.n_inputs,
                "gates": [gate.to_dict() for gate in self.gates], "outputs": list(self.outputs)}

    def to_json(self, *, indent: int | None = None) -> str:
        return json.dumps(self.to_dict(), sort_keys=True, separators=(",", ":") if indent is None else None,
                          indent=indent)

    def stable_hash(self) -> str:
        return hashlib.sha256(self.to_json().encode("utf-8")).hexdigest()

    @classmethod
    def from_dict(cls, value: Any, *, max_values: int = DEFAULT_MAX_VALUES,
                  max_outputs: int = DEFAULT_MAX_VALUES) -> Circuit:
        if not isinstance(value, dict) or set(value) != {"schema", "n_inputs", "gates", "outputs"}:
            raise ValueError("unexpected or missing circuit fields")
        if value["schema"] != SCHEMA:
            raise ValueError("unsupported circuit schema")
        n_inputs = _integer(value["n_inputs"], "n_inputs", 0)
        if not isinstance(value["gates"], list) or not isinstance(value["outputs"], list):
            raise ValueError("gates and outputs must be arrays")
        _limit(n_inputs + len(value["gates"]), max_values, "values")
        _limit(len(value["outputs"]), max_outputs, "outputs")
        return cls(n_inputs, tuple(Gate.from_dict(gate) for gate in value["gates"]),
                   tuple(value["outputs"]))

    @classmethod
    def from_json(cls, value: str, *, max_chars: int = 64 * 1024 * 1024, **limits: Any) -> Circuit:
        _limit(len(value), max_chars, "chars")
        return cls.from_dict(json.loads(value), **limits)


class CircuitBuilder:
    """Append gates while rejecting forward or nonexistent references."""

    def __init__(self, n_inputs: int, *, max_gates: int = DEFAULT_MAX_VALUES):
        self.n_inputs = _integer(n_inputs, "n_inputs", 0)
        self.max_gates = _integer(max_gates, "max_gates", 0)
        self.gates: list[Gate] = []

    def append(self, gate: Gate) -> int:
        available = self.n_inputs + len(self.gates)
        if not isinstance(gate, Gate):
            raise ValueError("expected a Gate")
        _limit(len(self.gates) + 1, self.max_gates, "gates")
        _reference(gate.a, available, "gate operand a")
        if gate.b is not None:
            _reference(gate.b, available, "gate operand b")
        self.gates.append(gate)
        return available

    def add(self, a: int, b: int) -> int:
        return self.append(Gate("add", a, b))

    def sub(self, a: int, b: int) -> int:
        return self.append(Gate("sub", a, b))

    def scale(self, coefficient: Any, a: int) -> int:
        return self.append(Gate("scale", a, coefficient=QI.coerce(coefficient)))

    def build(self, outputs: Iterable[int]) -> Circuit:
        return Circuit(self.n_inputs, tuple(self.gates), tuple(outputs))


def exact_matrix(matrix: Sequence[Sequence[Any]], *, rows: int | None = None,
                 columns: int | None = None, max_entries: int = DEFAULT_MAX_ENTRIES
                 ) -> tuple[tuple[QI, ...], ...]:
    """Validate dimensions and size before allocating exact coefficient objects."""
    nrows = len(matrix)
    ncols = len(matrix[0]) if nrows else (columns or 0)
    if rows is not None and nrows != rows:
        raise ValueError(f"expected {rows} matrix rows, got {nrows}")
    if columns is not None and ncols != columns:
        raise ValueError(f"expected {columns} matrix columns, got {ncols}")
    if any(len(row) != ncols for row in matrix):
        raise ValueError("matrix rows must have equal length")
    _limit(nrows * ncols, max_entries, "entries")
    return tuple(tuple(QI.coerce(value) for value in row) for row in matrix)


def matrix_digest(matrix: Sequence[Sequence[Any]], *, max_entries: int = DEFAULT_MAX_ENTRIES) -> str:
    matrix = exact_matrix(matrix, max_entries=max_entries)
    encoded = [[value.to_dict() for value in row] for row in matrix]
    data = json.dumps(encoded, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(data.encode("utf-8")).hexdigest()


def append_matrix(builder: CircuitBuilder, matrix: Sequence[Sequence[Any]],
                  inputs: Sequence[int]) -> tuple[int, ...]:
    """Dense exact matvec; omit zero/one scalings, negate with a subtract gate."""
    matrix = exact_matrix(matrix, columns=len(inputs))
    for ref in inputs:
        _reference(ref, builder.n_inputs + len(builder.gates), "matrix input")
    outputs = []
    for row in matrix:
        result = ZERO
        for coefficient, ref in zip(row, inputs):
            if coefficient == 0:
                continue
            if coefficient == 1:
                term = ref
            elif coefficient == -1:
                result = builder.sub(result, ref)
                continue
            else:
                term = builder.scale(coefficient, ref)
            result = term if result == ZERO else builder.add(result, term)
        outputs.append(result)
    return tuple(outputs)


def tensor_axis_circuit(matrix: Sequence[Sequence[Any]], k: int, *,
                        max_inputs: int = 4096, max_gates: int = 250_000) -> Circuit:
    """Build a scalar baseline for A tensor ... tensor A on lexicographic digits.

    Axis 0 is the most significant base-q digit. k=0 is the scalar identity.
    This dense-row implementation is a baseline, not an optimal circuit claim.
    """
    k = _integer(k, "k", 0)
    matrix = exact_matrix(matrix)
    q = len(matrix)
    if q == 0 or any(len(row) != q for row in matrix):
        raise ValueError("tensor kernel must be a nonempty square matrix")
    _integer(max_inputs, "max_inputs", 1)
    n = 1
    if q == 1:
        # Prevent a huge exponent from creating an impractically long program.
        _limit(k, max_gates, "gates")
    else:
        for _ in range(k):
            n *= q
            _limit(n, max_inputs, "inputs")
    builder = CircuitBuilder(n, max_gates=max_gates)
    values = list(range(n))
    for axis in range(k):
        stride = q ** (k - axis - 1)
        block = stride * q
        next_values = values.copy()
        for start in range(0, n, block):
            for offset in range(stride):
                positions = [start + offset + digit * stride for digit in range(q)]
                outputs = append_matrix(builder, matrix, [values[pos] for pos in positions])
                for pos, ref in zip(positions, outputs):
                    next_values[pos] = ref
        values = next_values
    return builder.build(values)

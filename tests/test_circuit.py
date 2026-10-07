from fractions import Fraction
import json
import unittest

from exact_fourier.circuit import Circuit, CircuitBuilder, Gate, ZERO, append_matrix, tensor_axis_circuit
from exact_fourier.scalars import GaussianRational as QI, I, ONE, ZERO as SCALAR_ZERO


C = ((QI(Fraction(1, 2), Fraction(1, 2)), QI(Fraction(1, 2), Fraction(-1, 2))),
     (QI(Fraction(1, 2), Fraction(-1, 2)), QI(Fraction(1, 2), Fraction(1, 2))))


def independent_tensor_matrix(matrix, k):
    """Direct entry formula, independent of the axis circuit builder."""
    q, n = len(matrix), len(matrix) ** k
    result = []
    for row in range(n):
        entries = []
        for col in range(n):
            coefficient = ONE
            a, b = row, col
            for _ in range(k):
                coefficient *= matrix[a % q][b % q]
                a //= q
                b //= q
            entries.append(coefficient)
        result.append(tuple(entries))
    return tuple(result)


class CircuitTests(unittest.TestCase):
    def test_chronological_program_and_free_aliases(self):
        builder = CircuitBuilder(2)
        total = builder.add(0, 1)
        difference = builder.sub(0, 1)
        rotated = builder.scale(I, difference)
        combined = builder.add(total, rotated)
        half = builder.scale(Fraction(1, 2), combined)
        circuit = builder.build((half, 1, ZERO, half))
        self.assertEqual((total, difference, rotated, combined, half), (2, 3, 4, 5, 6))
        self.assertEqual(circuit.gate_count, 5)
        self.assertEqual(circuit.operation_counts(), {"add": 2, "sub": 1, "scale": 2})
        self.assertEqual(circuit.evaluate((QI(2, 1), QI(1, -2))), (QI(0, 0), QI(1, -2), SCALAR_ZERO, SCALAR_ZERO))
        self.assertTrue(circuit.verify_matrix((C[0], (0, 1), (0, 0), C[0])))

    def test_exact_kernel_and_basis_certificate(self):
        builder = CircuitBuilder(2)
        circuit = builder.build(append_matrix(builder, C, (0, 1)))
        self.assertEqual(circuit.linear_matrix(), C)
        certificate = circuit.linear_map_certificate(C)
        self.assertTrue(certificate["passed"])
        self.assertEqual(certificate["basis_inputs_checked"], 2)
        self.assertEqual(certificate["entries_checked"], 4)
        self.assertEqual(certificate["actual_matrix_sha256"], certificate["expected_matrix_sha256"])
        self.assertFalse(circuit.verify_matrix(((1, 0), (0, 1))))
        for x in ((1, 0), (0, 1), (QI(2, 3), QI(-4, 7))):
            expected = tuple(sum((coefficient * value for coefficient, value in zip(row, x)), SCALAR_ZERO)
                             for row in C)
            self.assertEqual(circuit.evaluate(x), expected)

    def test_all_emitted_scalings_cost_gates(self):
        builder = CircuitBuilder(1)
        identity = builder.scale(1, 0)
        negative = builder.scale(-1, identity)
        zero = builder.scale(0, negative)
        circuit = builder.build((identity, negative, zero))
        self.assertEqual(circuit.gate_count, 3)
        self.assertEqual(circuit.evaluate((QI(2, 3),)), (QI(2, 3), QI(-2, -3), SCALAR_ZERO))

    def test_invalid_references_are_rejected_before_execution(self):
        for gate in (Gate("add", 0, 2), Gate("sub", -2, 0), Gate("scale", 3, coefficient=I)):
            with self.assertRaisesRegex(ValueError, "unavailable"):
                Circuit(2, (gate,), (0,))
        with self.assertRaises(ValueError):
            Circuit(1, (), (1,))
        builder = CircuitBuilder(2)
        with self.assertRaises(ValueError):
            builder.add(0, 2)
        with self.assertRaises(ValueError):
            builder.sub(True, 0)
        with self.assertRaises(ValueError):
            Gate("add", 0, 1, coefficient=I)
        with self.assertRaises(ValueError):
            Gate("divide", 0, 1)

    def test_json_roundtrip_stable_hash_and_reject_invalid_import(self):
        circuit = tensor_axis_circuit(C, 2)
        clone = Circuit.from_json(circuit.to_json(indent=2))
        self.assertEqual(clone, circuit)
        self.assertEqual(clone.stable_hash(), circuit.stable_hash())
        self.assertEqual(len(circuit.stable_hash()), 64)
        self.assertEqual(clone.linear_matrix(), independent_tensor_matrix(C, 2))
        encoded = circuit.to_dict()
        encoded["gates"][0]["a"] = 10_000
        with self.assertRaises(ValueError):
            Circuit.from_dict(encoded)
        encoded = circuit.to_dict()
        encoded["schema"] = "unsupported"
        with self.assertRaises(ValueError):
            Circuit.from_dict(encoded)
        encoded = circuit.to_dict()
        encoded["extra"] = 1
        with self.assertRaises(ValueError):
            Circuit.from_dict(encoded)

    def test_resource_limits_precede_materialization(self):
        circuit = tensor_axis_circuit(C, 2)
        with self.assertRaisesRegex(ValueError, "entries"):
            circuit.linear_matrix(max_entries=15)
        with self.assertRaisesRegex(ValueError, "work"):
            circuit.linear_matrix(max_work=1)
        with self.assertRaisesRegex(ValueError, "values"):
            circuit.evaluate((0, 0, 0, 0), max_values=4)
        with self.assertRaisesRegex(ValueError, "values"):
            Circuit.from_dict(circuit.to_dict(), max_values=4)
        with self.assertRaisesRegex(ValueError, "chars"):
            Circuit.from_json(circuit.to_json(), max_chars=1)
        with self.assertRaisesRegex(ValueError, "outputs"):
            Circuit(0, (), (ZERO, ZERO)).evaluate((), max_values=1)
        builder = CircuitBuilder(1, max_gates=0)
        with self.assertRaisesRegex(ValueError, "gates"):
            builder.add(0, 0)
        with self.assertRaisesRegex(ValueError, "inputs"):
            tensor_axis_circuit(C, 20)
        builder = CircuitBuilder(1)
        enormous = builder.scale(2 ** 100, 0)
        with self.assertRaisesRegex(ValueError, "bit length"):
            builder.build((enormous,)).evaluate((1,), max_bits=50)

    def test_tensor_axis_baseline_matches_independent_exact_entries(self):
        for matrix in (C, ((1, 2), (-1, 3)), ((1, 0, I), (0, 1, 0), (-I, 2, 1))):
            for k in range(4 if len(matrix) == 2 else 3):
                with self.subTest(q=len(matrix), k=k):
                    circuit = tensor_axis_circuit(matrix, k)
                    self.assertTrue(circuit.verify_matrix(independent_tensor_matrix(matrix, k)))
        self.assertEqual(tensor_axis_circuit(C, 0), Circuit(1, (), (0,)))
        self.assertEqual(tensor_axis_circuit(((I,),), 4).evaluate((1,)), (ONE,))

    def test_zero_matrix_and_empty_linear_map(self):
        builder = CircuitBuilder(2)
        circuit = builder.build(append_matrix(builder, ((0, 0), (0, 0)), (0, 1)))
        self.assertEqual(circuit.gate_count, 0)
        self.assertTrue(circuit.verify_matrix(((0, 0), (0, 0))))
        self.assertTrue(Circuit(0, (), (ZERO,)).verify_matrix(((),)))
        self.assertEqual(Circuit(0).linear_matrix(), ())
        with self.assertRaises(ValueError):
            circuit.evaluate((0,))
        with self.assertRaises(ValueError):
            circuit.verify_matrix(((0,), (0,)))


if __name__ == "__main__":
    unittest.main()

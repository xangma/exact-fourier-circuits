"""Exact intertwining identities and dirty-data execution of the full quotient."""

import unittest
from fractions import Fraction

from exact_fourier.directional import directional_word
from exact_fourier.gf2 import SparseBinaryVector, SparseTensorDirection
from exact_fourier.projection import (BinaryProjection, build_projected_program,
                                     evaluate_projected_exact, projected_target_exact,
                                     random_projection)
from exact_fourier.scalars import GaussianRational as QI
from exact_fourier.words import A, B, KERNEL_C, tensor_axis_word


def literal_directional(values, mask, inverse=False):
    a, b = (B, A) if inverse else (A, B)
    return tuple(a * value + b * values[address ^ mask] for address, value in enumerate(values))


def dirty_values(program):
    """Nonzero dyadic real/imaginary data in every role, including all padding."""
    roles, width = program.metadata["roles"], program.metadata["width"]
    return tuple(tuple(QI(Fraction((17 * role + 5 * address) % 29 - 14, 8),
                          Fraction((11 * role + 7 * address) % 31 - 15, 16))
                       for address in range(width)) for role in range(roles))


class ProjectionIdentityTests(unittest.TestCase):
    def test_surjectivity_and_domain_guards(self):
        projection = BinaryProjection((1, 2, 3), 2)
        self.assertEqual({projection.project(x) for x in range(8)}, set(range(4)))
        with self.assertRaises(ValueError):
            BinaryProjection((1, 1), 2)
        with self.assertRaises(ValueError):
            BinaryProjection((1, 2, 4), 2)
        with self.assertRaises(ValueError):
            projection.project(8)
        with self.assertRaises(ValueError):
            random_projection(2, 3)
        with self.assertRaises(ValueError):
            build_projected_program(bits=30)
        with self.assertRaises(ValueError):
            build_projected_program(h=22)

    def test_all_reduced_basis_vectors_intertwine_actual_direction_words(self):
        projection = BinaryProjection((1, 2, 3), 2)
        # All four reduced basis vectors, all odd source directions in dimension
        # three, both signs. z=111 projects to zero and remains an identity.
        for support in ((0,), (1,), (2,), (0, 1, 2)):
            direction = SparseTensorDirection((SparseBinaryVector(3, support),))
            mask = projection.direction_mask(direction)
            for inverse in (False, True):
                source = directional_word(direction, inverse=inverse).compile()
                for basis in range(4):
                    reduced = tuple(QI(int(address == basis)) for address in range(4))
                    pulled_back = projection.pullback(reduced)
                    actual = source.evaluate(pulled_back)
                    expected = projection.pullback(literal_directional(reduced, mask, inverse))
                    self.assertEqual(actual, expected)

    def test_all_reduced_basis_vectors_intertwine_full_tensor_target(self):
        projection = BinaryProjection((1, 2, 3), 2)
        source = tensor_axis_word(KERNEL_C, 3).compile()
        for basis in range(4):
            reduced = tuple(QI(int(address == basis)) for address in range(4))
            projected = reduced
            for image in projection.images:
                projected = literal_directional(projected, image)
            self.assertEqual(source.evaluate(projection.pullback(reduced)), projection.pullback(projected))

    def test_column_offset_uses_distinct_projected_kernels(self):
        projection = BinaryProjection((1, 2, 3, 2, 1, 0), 2)
        direction = SparseTensorDirection((SparseBinaryVector(3, (0, 1, 2)),))
        self.assertEqual(projection.direction_mask(direction, 0), 0)
        self.assertEqual(projection.direction_mask(direction, 1), 3)
        # Products C_1 C_2 are not generally C_(1 XOR 2).
        values = (QI(1), QI(0), QI(0), QI(0))
        self.assertNotEqual(literal_directional(literal_directional(values, 1), 2), literal_directional(values, 3))


class FullProjectedNetworkTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.padded = build_projected_program(bits=1)
        cls.unpadded = build_projected_program(bits=2, include_padding=False)

    def test_all_dirty_roles_compiled_shears_equal_independent_target(self):
        program = self.padded
        values = dirty_values(program)
        expected = projected_target_exact(program, values)
        actual = evaluate_projected_exact(program, values, compiled_shears=True, capture_checkpoints=True)
        self.assertEqual(actual.final, expected)
        self.assertEqual(tuple(label for label, _ in actual.checkpoints),
                         tuple(checkpoint.label for checkpoint in program.checkpoints))
        self.assertTrue(all(len(rows) == 1024 and all(len(row) == 2 for row in rows)
                            for _, rows in actual.checkpoints))

    def test_four_address_values_full_original_network_equal_independent_target(self):
        program = self.unpadded
        values = dirty_values(program)
        actual = evaluate_projected_exact(program, values, compiled_shears=False)
        self.assertEqual(actual.final, projected_target_exact(program, values))

    def test_padding_budget_and_stage_boundaries(self):
        program = self.padded
        metadata = program.metadata
        self.assertEqual(metadata["roles"], 1024)
        self.assertEqual(metadata["original_roles"], 944)
        self.assertEqual(metadata["bank_size"], 64)
        self.assertEqual(metadata["role_bits"], 10)
        self.assertEqual(len(program.records), 72842)
        self.assertEqual(sum(record[0] == 1 for record in program.records), 5376)
        self.assertEqual(sum(record[0] == 0 for record in program.records), 62208 + 80 * 64)
        self.assertEqual(sum(record[0] == 4 for record in program.records), 10)
        self.assertEqual(tuple(c.label for c in program.checkpoints),
                         ("stage_1", "stage_2", "stage_3", "terminal_translation",
                          "terminal_bank_exchange", "padding", "role_axes"))
        self.assertEqual(program.checkpoints[-1].record_index, len(program.records))
        self.assertTrue(all(a.record_index < b.record_index
                            for a, b in zip(program.checkpoints, program.checkpoints[1:])))
        for next_stage, checkpoint in enumerate(program.checkpoints[:2], 1):
            # The first new-stage operation touches its distinct side auxiliary;
            # the checkpoint excludes it rather than lagging into that stage.
            op, role, _, _, _, _ = program.records[checkpoint.record_index]
            self.assertEqual(op, 0)
            self.assertEqual((role - 128) // 17 // 16, next_stage)

    def test_zero_direction_records_are_preserved(self):
        program = build_projected_program(bits=0, include_padding=False)
        directions = [record for record in program.records if record[0] == 0]
        self.assertEqual(len(directions), 62208)
        self.assertTrue(all(record[2] == 0 for record in directions))
        self.assertEqual(program.metadata["zero_direction_records"], 62208)
        self.assertEqual(len(program.records), 67712)

    def test_default_program_schema_and_projection_identity_minor(self):
        program = build_projected_program()
        data = program.to_dict()
        self.assertEqual(data["schema"], "exact-fourier-projected-program/v1")
        self.assertEqual(data["projection"]["images"][:6], [1, 2, 4, 8, 16, 32])
        self.assertEqual(data["metadata"]["width"], 64)
        self.assertEqual(data["records"][0][0], 1)
        self.assertEqual(data["checkpoints"][-1]["record_index"], len(program.records))

    def test_two_column_full_network_keeps_separate_kernel_factors(self):
        program = build_projected_program(bits=1, columns=2)
        self.assertEqual(len(program.records), 140170)
        self.assertEqual(sum(record[0] == 0 for record in program.records), 2 * 62208 + 80 * 128)
        values = dirty_values(program)
        actual = evaluate_projected_exact(program, values, compiled_shears=False)
        self.assertEqual(actual.final, projected_target_exact(program, values))


if __name__ == "__main__":
    unittest.main()

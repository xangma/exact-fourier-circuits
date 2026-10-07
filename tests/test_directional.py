"""Exact primitive checks independent of the complete seed's enormous width."""

from fractions import Fraction
from itertools import product
import random
import unittest

from exact_fourier.directional import (apply_directional_exact, directional_word,
                                       expand_directional_step)
from exact_fourier.gf2 import SparseBinaryVector as V, SparseTensorDirection as T
from exact_fourier.network import DirectionalStep
from exact_fourier.scalars import GaussianRational as QI, I, ONE, ZERO
from exact_fourier.words import A, B, Call, Permute


def independent_expected_matrix(direction, columns, inverse):
    """Expand product(A I+B R) without using address pair enumeration."""
    width = 2 ** (direction.dimension * columns)
    base_mask = sum(2 ** index for index in direction.iter_ones())
    masks = [base_mask * (2 ** (column * direction.dimension)) for column in range(columns)]
    a, b = (B, A) if inverse else (A, B)
    matrix = [[ZERO for _ in range(width)] for _ in range(width)]
    for row in range(width):
        for choices in product((0, 1), repeat=columns):
            translation, coefficient = 0, ONE
            for choice, mask in zip(choices, masks):
                if choice:
                    translation ^= mask
                    coefficient *= b
                else:
                    coefficient *= a
            matrix[row][row ^ translation] += coefficient
    return tuple(tuple(row) for row in matrix)


class DirectionalTests(unittest.TestCase):
    def test_exact_full_matrix_forward_and_inverse_random_odd_directions(self):
        rng = random.Random(130)
        for dimension in range(1, 5):
            odd_supports = [tuple(i for i in range(dimension) if bits >> i & 1)
                            for bits in range(1, 2 ** dimension) if bits.bit_count() & 1]
            for support in rng.sample(odd_supports, min(3, len(odd_supports))):
                direction = T((V(dimension, support),))
                for columns in (1, 2):
                    for inverse in (False, True):
                        with self.subTest(dimension=dimension, support=support, columns=columns, inverse=inverse):
                            word = directional_word(direction, columns, inverse)
                            expected = independent_expected_matrix(direction, columns, inverse)
                            self.assertTrue(word.compile().verify_matrix(expected))
                            self.assertEqual(word.call_count, columns * word.width // 2)
                            self.assertEqual(sum(isinstance(s, Permute) for s in word.steps), int(inverse))

    def test_call_pairs_partition_each_column_and_pivot_is_zero(self):
        direction = T((V(3, (0, 1, 2)),))
        word = directional_word(direction, 2)
        per_column = word.width // 2
        for column in range(2):
            steps = word.steps[column * per_column:(column + 1) * per_column]
            mask = 0b111 << (3 * column)
            addresses = []
            for step in steps:
                self.assertIsInstance(step, Call)
                x, y = step.coordinates
                self.assertEqual(x ^ y, mask)
                self.assertEqual(x & (1 << (3 * column)), 0)
                addresses.extend((x, y))
            self.assertEqual(sorted(addresses), list(range(word.width)))

    def test_inverse_permutation_translates_all_column_masks(self):
        direction = T((V(3, (0, 1, 2)),))
        word = directional_word(direction, 2, True)
        expected_mask = 0b111111
        self.assertEqual(word.steps[-1], Permute(tuple(i ^ expected_mask for i in range(64))))
        original = tuple(QI(Fraction(i - 17, 3), Fraction(i % 7 - 3, 5)) for i in range(64))
        forward = directional_word(direction, 2).compile().evaluate(original)
        self.assertEqual(word.compile().evaluate(forward), original)
        self.assertEqual(word.compile().evaluate(original), apply_directional_exact(original, direction, 2, True))

    def test_tensor_support_uses_row_major_positions_as_lsb_address_bits(self):
        # Flattened support is position 1*3+2=5, so the address xor is bit 5.
        direction = T((V.unit(2, 1), V.unit(3, 2)))
        self.assertEqual(tuple(direction.iter_ones()), (5,))
        word = directional_word(direction)
        self.assertTrue(all(step.coordinates[0] ^ step.coordinates[1] == 32 for step in word.steps))
        self.assertTrue(word.compile().verify_matrix(independent_expected_matrix(direction, 1, False)))

    def test_every_walsh_character_gets_exact_phase(self):
        for direction, columns in ((T((V(3, (0, 1, 2)),)), 1),
                                   (T((V(3, (0, 1, 2)),)), 2),
                                   (T((V.unit(2, 1),)), 2)):
            width = 2 ** (direction.dimension * columns)
            base_mask = sum(1 << index for index in direction.iter_ones())
            for inverse in (False, True):
                circuit = directional_word(direction, columns, inverse).compile()
                for frequency in range(width):
                    values = tuple(QI(-1 if (frequency & address).bit_count() & 1 else 1)
                                   for address in range(width))
                    exponent = sum((frequency & (base_mask << (column * direction.dimension))).bit_count() & 1
                                   for column in range(columns))
                    phase = I ** (-exponent if inverse else exponent)
                    self.assertEqual(circuit.evaluate(values), tuple(phase * value for value in values))

    def test_directional_step_role_is_external(self):
        direction = T((V(3, (0, 1, 2)),))
        step = DirectionalStep(1_000_000, direction, 2, True)
        self.assertEqual(expand_directional_step(step), directional_word(direction, 2, True))
        with self.assertRaises(ValueError):
            expand_directional_step(DirectionalStep(-1, direction, 1, False))

    def test_oversized_space_rejected_before_mask_support_expansion(self):
        class ExplosiveSupport(T):
            def iter_ones(self):
                raise AssertionError("support must not be materialized before the size check")
        direction = ExplosiveSupport((V(10 ** 12, (0, 1, 2)),))
        with self.assertRaisesRegex(ValueError, "limit"):
            directional_word(direction, 10 ** 30)
        # Separate bit cap continues to protect a caller-supplied huge input cap.
        with self.assertRaisesRegex(ValueError, "limit"):
            directional_word(direction, max_inputs=1 << 100, max_address_bits=16)
        with self.assertRaisesRegex(ValueError, "call limit"):
            directional_word(T((V.unit(4, 0),)), 2, max_calls=255)
        with self.assertRaisesRegex(ValueError, "input"):
            directional_word(T((V.unit(4, 0),)), 2, max_inputs=255)

    def test_reject_invalid_norm_columns_inverse_and_values(self):
        for direction in (T((V(3, (0, 1)),)), T((V.zero(0),))):
            with self.assertRaises(ValueError):
                directional_word(direction)
        direction = T((V.unit(3, 0),))
        for columns in (0, -1, True, 1.0):
            with self.assertRaises(ValueError):
                directional_word(direction, columns)
        with self.assertRaises(ValueError):
            directional_word(direction, inverse=1)
        with self.assertRaises(ValueError):
            apply_directional_exact((1,), direction)


if __name__ == "__main__":
    unittest.main()

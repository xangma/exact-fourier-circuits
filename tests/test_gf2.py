from itertools import islice
import unittest

from exact_fourier.gf2 import (NoOrthonormalBasisError, SparseBinaryVector as V,
                               SparseTensorDirection, full_coordinate_basis,
                               orthonormal_basis_complement, transvection)


def rank(vectors):
    """Independent small-case Gaussian elimination using packed integers."""
    pivots = {}
    for vector in vectors:
        word = sum(1 << index for index in vector.ones)
        while word:
            pivot = word.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = word
                break
            word ^= pivots[pivot]
    return len(pivots)


class SparseBinaryTests(unittest.TestCase):
    def assert_frame(self, seeds):
        complement = tuple(orthonormal_basis_complement(seeds))
        frame = tuple(seeds) + complement
        self.assertEqual(len(frame), seeds[0].dimension)
        for i, left in enumerate(frame):
            for j, right in enumerate(frame):
                self.assertEqual(left.dot(right), int(i == j))
        self.assertEqual(rank(frame), seeds[0].dimension)
        return complement

    def test_sparse_dot_xor_and_validation(self):
        a, b = V(10, (0, 3, 7)), V(10, (1, 3, 6))
        self.assertEqual(a.dot(b), 1)
        self.assertEqual(a.xor(b), V(10, (0, 1, 6, 7)))
        self.assertEqual(a ^ a, V.zero(10))
        self.assertEqual(a.norm, 1)
        self.assertEqual(a.weight_mod4, 3)
        self.assertTrue(a.contains(7))
        self.assertFalse(a.contains(6))
        self.assertEqual(V.from_indices(10, (7, 0, 3)), a)
        for support in ((1, 1), (3, 0), (-1,), (10,), (True,)):
            with self.assertRaises(ValueError):
                V(10, support)
        with self.assertRaises(ValueError):
            a.dot(V(9, (0,)))
        with self.assertRaises(ValueError):
            a.contains(10)

    def test_transvection_preserves_all_small_dot_products(self):
        v = V(4, (0, 1))
        all_vectors = [V(4, tuple(i for i in range(4) if bits >> i & 1)) for bits in range(16)]
        for left in all_vectors:
            self.assertEqual(transvection(v, transvection(v, left)), left)
            for right in all_vectors:
                self.assertEqual(transvection(v, left).dot(transvection(v, right)), left.dot(right))
        with self.assertRaises(ValueError):
            transvection(V.unit(4, 0), V.unit(4, 1))

    def test_complement_of_triple_and_orthogonal_triple_pair(self):
        self.assert_frame((V(7, (0, 1, 2)),))
        self.assert_frame((V(7, (0, 1, 2)), V(7, (3, 4, 5))))
        self.assert_frame((V(7, (0, 1, 2)), V(7, (0, 1, 3))))
        self.assert_frame((V(100, (0, 1, 2)), V(100, (3, 4, 5))))

    def test_every_small_orthonormal_one_or_two_seed_layout(self):
        for dimension in range(1, 7):
            odd = [V(dimension, tuple(i for i in range(dimension) if bits >> i & 1))
                   for bits in range(1 << dimension) if bits.bit_count() & 1]
            for u in odd:
                if u.weight == dimension and dimension > 1:
                    with self.assertRaises(NoOrthonormalBasisError):
                        tuple(orthonormal_basis_complement((u,)))
                else:
                    self.assert_frame((u,))
                for y in odd:
                    if u.dot(y):
                        continue
                    if u.xor(y).weight == dimension and dimension > 2:
                        with self.assertRaises(NoOrthonormalBasisError):
                            tuple(orthonormal_basis_complement((u, y)))
                    else:
                        self.assert_frame((u, y))

    def test_zero_complement_and_alternating_failure(self):
        self.assertEqual(tuple(orthonormal_basis_complement((V.unit(1, 0),))), ())
        self.assertEqual(tuple(orthonormal_basis_complement((V.unit(2, 0), V.unit(2, 1)))), ())
        with self.assertRaisesRegex(NoOrthonormalBasisError, "alternating"):
            tuple(orthonormal_basis_complement((V(3, (0, 1, 2)),)))
        with self.assertRaisesRegex(NoOrthonormalBasisError, "u.y"):
            tuple(orthonormal_basis_complement((V(4, (0,)), V(4, (1, 2, 3)))))
        for seeds in ((), (V(2, (0, 1)),), (V.unit(3, 0), V(3, (0, 1, 2))),
                      (V.unit(2, 0), V.unit(3, 1))):
            with self.assertRaises(ValueError):
                tuple(orthonormal_basis_complement(seeds))

    def test_large_dimension_basis_is_lazy(self):
        first = tuple(islice(full_coordinate_basis(10 ** 12), 3))
        self.assertEqual([v.ones for v in first], [(0,), (1,), (2,)])
        triple = V(10 ** 12, (0, 1, 2))
        complement = tuple(islice(orthonormal_basis_complement((triple,)), 3))
        self.assertEqual(len(complement), 3)
        self.assertTrue(all(v.weight <= 3 for v in complement))
        self.assertTrue(all(v.dot(triple) == 0 and v.norm == 1 for v in complement))

    def test_tensor_support_flattening_and_parity(self):
        a, b = V(7, (0, 2, 5)), V(7, (1, 3, 6))
        tensor = SparseTensorDirection((a, b))
        expected = tuple(i * 7 + j for i in a.ones for j in b.ones)
        self.assertEqual(tensor.dimension, 49)
        self.assertEqual(tensor.weight, 9)
        self.assertEqual(tensor.norm, 1)
        self.assertEqual(tensor.weight_mod4, 1)
        self.assertEqual(tuple(tensor.iter_ones()), expected)
        self.assertTrue(tensor.same_shape((7, 7)))
        for index in range(49):
            self.assertEqual(tensor.contains(index), index in expected)
        direct = V(49, expected)
        self.assertEqual(direct.norm, tensor.norm)
        self.assert_frame((direct,))

    def test_tensor_empty_zero_and_huge_dimension(self):
        scalar = SparseTensorDirection(())
        self.assertEqual((scalar.dimension, scalar.weight, scalar.norm), (1, 1, 1))
        self.assertEqual(tuple(scalar.iter_ones()), (0,))
        self.assertTrue(scalar.contains(0))
        empty = SparseTensorDirection((V.zero(7), V.unit(2, 0)))
        self.assertEqual(tuple(empty.iter_ones()), ())
        self.assertEqual(empty.norm, 0)
        huge = SparseTensorDirection((V(10 ** 12, (0, 2, 9)),) * 5)
        self.assertEqual(huge.dimension, 10 ** 60)
        self.assertEqual(huge.weight, 243)
        self.assertEqual(huge.weight_mod4, 3)
        self.assertEqual(tuple(islice(huge.iter_ones(), 3)), (0, 2, 9))
        self.assertTrue(huge.contains(9))
        self.assertFalse(huge.contains(10))
        with self.assertRaises(ValueError):
            huge.contains(huge.dimension)
        zero_space = SparseTensorDirection((V.zero(0),))
        self.assertEqual(tuple(zero_space.iter_ones()), ())
        with self.assertRaises(ValueError):
            zero_space.contains(0)


if __name__ == "__main__":
    unittest.main()

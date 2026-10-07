"""Focused exact checks of the constructive network and its symbolic budget."""

import unittest
from fractions import Fraction
from itertools import combinations, islice

from exact_fourier.gf2 import SparseBinaryVector
from exact_fourier.network import (DirectionalStep, FactoredCount, NetworkParameters,
                                   PointwiseShear, Residual, TerminalCorrection,
                                   apply_network_walsh_mode, apply_scalar_network, iter_network_program,
                                   iter_scalar_shears, saving_seed_plan)
from exact_fourier.scalars import GaussianRational


class NetworkTests(unittest.TestCase):
    def test_triple_neighbors_and_ordered_side_ranks(self):
        for h in range(3, 9):
            p = NetworkParameters(h)
            triples = list(combinations(range(h), 3))
            self.assertEqual([p.triple(i) for i in range(p.v)], triples)
            for index, triple in enumerate(triples):
                self.assertEqual(p.triple_index(triple), index)
                neighbors = list(p.neighbors(index))
                expected = {j for j, other in enumerate(triples) if len(set(triple).intersection(other)) % 2 == 0}
                self.assertEqual(set(neighbors), expected)
                self.assertEqual(len(neighbors), p.degree)
                self.assertEqual([p.neighbor_index(index, j) for j in neighbors], list(range(p.degree)))

    def test_rg_plus_jv_exact_identity(self):
        for h in (3, 4, 7):
            p = NetworkParameters(h)
            for s in range(p.v):
                neighbors = set(p.neighbors(s))
                for t in range(p.v):
                    intersection = len(set(p.triple(s)).intersection(p.triple(t)))
                    rg = Fraction(intersection - 1, 2)
                    jv = -rg if t in neighbors else Fraction(0)
                    self.assertEqual(rg + jv, int(s == t))

    def test_each_invocation_restores_dirty_auxiliaries(self):
        p = NetworkParameters(4)
        original = [Fraction((i * 17) % 29 - 14, (i % 7) + 1) for i in range(p.wires)]
        for stage in range(3):
            invocation = p.invocation(stage, (1, 2))
            actual = list(original)
            shears = list(invocation.shears())
            self.assertEqual(len(shears), 4 * p.v * p.degree + 16 * p.v)
            for shear in shears:
                self.assertNotEqual(shear.source, shear.target)
                self.assertNotEqual(shear.coefficient, 0)
                actual[shear.target] += shear.coefficient * actual[shear.source]
            expected = list(original)
            for entry in range(p.v):
                x, y = invocation.bank("X", entry), invocation.bank("Y", entry)
                if stage == 1:
                    expected[x] -= original[y]
                else:
                    expected[y] += original[x]
            self.assertEqual(actual, expected)

    def test_complete_scalar_exchange_on_every_basis_vector(self):
        # At h=3 this checks every entry of the scalar network's matrix.
        p = NetworkParameters(3)
        for column in range(p.wires):
            original = [Fraction(int(row == column)) for row in range(p.wires)]
            expected = list(original)
            expected[:p.bank_size] = [-v for v in original[p.bank_size:2 * p.bank_size]]
            expected[p.bank_size:2 * p.bank_size] = original[:p.bank_size]
            self.assertEqual(apply_scalar_network(original, p), expected)

    def test_complex_data_exchange_and_arbitrary_auxiliaries(self):
        p = NetworkParameters(4)
        original = [GaussianRational(Fraction(i % 13 - 6, 3), Fraction(i % 17 - 8, 5)) for i in range(p.wires)]
        expected = list(original)
        expected[:p.bank_size] = [-v for v in original[p.bank_size:2 * p.bank_size]]
        expected[p.bank_size:2 * p.bank_size] = original[:p.bank_size]
        self.assertEqual(apply_scalar_network(original, p), expected)
        self.assertEqual(sum(1 for _ in iter_scalar_shears(p)), p.scalar_shears)

    def test_residual_sparse_bases_dimensions_and_orthogonality(self):
        p = NetworkParameters(4)
        kinds = ("B_t", "B_tperp", "B_D", "P_tperp", "P_D", "P_t", "side_0_2", "P_pairperp", "terminal_aux")
        for stage in range(3):
            invocation = p.invocation(stage, (1, 2))
            for kind in kinds:
                residual = Residual(kind, x_entry=0, y_entry=1)
                basis = list(residual.basis(invocation))
                self.assertEqual(len(basis), residual.dimension(invocation))
                sparse = [SparseBinaryVector(direction.dimension, tuple(direction.iter_ones())) for direction in basis]
                self.assertTrue(all(vector.norm == 1 and vector.dimension == p.m for vector in sparse))
                self.assertTrue(all(a.dot(b) == 0 for a, b in combinations(sparse, 2)))

    def test_lazy_network_counts_match_full_dimension_budget(self):
        # Streams ~60k symbolic directions; never constructs any 2^64 arrays.
        p = NetworkParameters(4)
        directions = shears = corrections = 0
        for instruction in iter_network_program(p):
            if isinstance(instruction, DirectionalStep):
                directions += 1
                self.assertEqual(instruction.direction.norm, 1)
                if instruction.role < 2 * p.bank_size:
                    self.assertEqual(instruction.inverse, instruction.direction.weight_mod4 == 3)
            elif isinstance(instruction, PointwiseShear):
                shears += 1
                self.assertEqual(instruction.address_bits, p.m)
            elif isinstance(instruction, TerminalCorrection):
                corrections += 1
                self.assertEqual(len(list(instruction.exceptional_translations())), p.bank_size)
                self.assertEqual(len(list(instruction.signed_bank_pairs())), p.bank_size)
        self.assertEqual(directions, p.residual_dimensions)
        self.assertEqual(shears, p.scalar_shears)
        self.assertEqual(corrections, 1)
        self.assertLess(p.delta, 0)  # This small executable model makes no saving claim.

    def test_complete_framed_network_on_exact_walsh_modes(self):
        p = NetworkParameters(4)
        original = [GaussianRational(Fraction(i % 7 - 3, 3), Fraction(i % 11 - 5, 7)) for i in range(p.wires)]
        phases = (GaussianRational(1), GaussianRational(0, 1), GaussianRational(-1), GaussianRational(0, -1))
        # Sparse, dense, and multicolumn characters exercise inverse directions,
        # frame cancellation, exceptional translations and the signed bank swap.
        for frequencies in ((1,), (0xDEADBEEF01234567,), ((1 << 64) - 1,), (0x0123456789ABCDEF, 0x0F0F0F0F0F0F0F0F)):
            phase = phases[sum(frequency.bit_count() for frequency in frequencies) % 4]
            expected = [phase * value for value in original]
            self.assertEqual(apply_network_walsh_mode(original, p, frequencies), expected)

    def test_paper_seed_exact_budget_and_minimal_column_count(self):
        plan = saving_seed_plan()
        p = plan.parameters
        self.assertEqual(p.wires, 1873807244643542670000)
        self.assertEqual(p.residual_dimensions, 1873807244636671267308000000)
        self.assertEqual(p.delta, 6871402692000000)
        self.assertEqual(plan.H, 22486194194905980000000)
        self.assertEqual(plan.f, 6544863)
        self.assertEqual(plan.b, 6544863000071)
        self.assertEqual(plan.padded_roles, 1 << 71)
        self.assertEqual(plan.calls.coefficient + plan.saved_calls.coefficient, plan.ordinary_calls.coefficient)
        self.assertGreater(plan.saved_calls.coefficient, 0)
        self.assertLessEqual(p.delta * (plan.f - 1), 2 * plan.H)
        self.assertFalse(plan.expanded)
        self.assertFalse(plan.kernel_verified)
        with self.assertRaises(ValueError):
            plan.calls.to_int()
        # A prefix prints immediately, with no expansion of enormous array widths.
        prefix = list(islice(plan.instructions(), 2))
        self.assertTrue(all(isinstance(step, PointwiseShear) for step in prefix))

    def test_parameter_and_count_guards(self):
        for h in (2, 4.0, True):
            with self.assertRaises(ValueError):
                NetworkParameters(h)
        for h in (4, 21):
            with self.assertRaises(ValueError):
                saving_seed_plan(h)
        with self.assertRaises(ValueError):
            saving_seed_plan(f=1)
        with self.assertRaises(ValueError):
            saving_seed_plan(f=6544863.0)
        self.assertEqual(FactoredCount(5, 3).to_int(), 40)


if __name__ == "__main__":
    unittest.main()

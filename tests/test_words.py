import unittest
from exact_fourier.scalars import GaussianRational as QI, I
from exact_fourier.words import (KERNEL_C, Word, Call, Scale, Permute, shear_steps,
    tensor_axis_word, tensor_matrix, verify_finite_win)


class WordTests(unittest.TestCase):
    def test_kernel_four_gate_implementation(self):
        c=Word(KERNEL_C,2,(Call((0,1)),)).compile()
        self.assertEqual(c.gate_count,4)
        self.assertTrue(c.verify_matrix(KERNEL_C))

    def test_three_call_shear_all_basis_vectors(self):
        for t in (QI(1),QI('-1/2'),QI(3,2),I):
            w=Word(KERNEL_C,3,shear_steps(2,0,t))
            self.assertEqual(w.call_count,3)
            self.assertTrue(w.compile().verify_matrix(((1,0,0),(0,1,0),(t,0,1))))

    def test_fixed_six_call_zero_and_complex(self):
        for t in (QI(0),QI(1),QI(3,-2)):
            w=Word(KERNEL_C,2,shear_steps(0,1,t,fixed_six_calls=True))
            self.assertEqual(w.call_count,6)
            self.assertTrue(w.compile().verify_matrix(((1,t),(0,1))))

    def test_inverse_is_swap_times_forward(self):
        w=Word(KERNEL_C,2,(Call((0,1)),Permute((1,0)),Call((0,1))))
        self.assertTrue(w.compile().verify_matrix(((1,0),(0,1))))

    def test_tensor_baseline_matches_independent_entry_formula(self):
        for k in (1,2,3):
            w=tensor_axis_word(KERNEL_C,k)
            self.assertEqual(w.call_count,k*2**(k-1))
            self.assertTrue(w.compile().verify_matrix(tensor_matrix(KERNEL_C,k)))

    def test_candidate_requires_saving_and_correct_identity(self):
        with self.assertRaisesRegex(ValueError,'strictly save'):
            verify_finite_win(tensor_axis_word(KERNEL_C,2),2)
        wrong=Word(KERNEL_C,4,(Call((0,1)),))
        with self.assertRaisesRegex(ValueError,'exact tensor power'):
            verify_finite_win(wrong,2)

    def test_exact_json_roundtrip(self):
        w=Word(KERNEL_C,2,shear_steps(0,1,QI(2,1)))
        self.assertEqual(Word.from_dict(w.to_dict()),w)

    def test_reject_invalid_word(self):
        with self.assertRaises(ValueError): Scale(0,0)
        with self.assertRaises(ValueError): Call((0,0))
        with self.assertRaises(ValueError): Word(KERNEL_C,2,(Call((0,2)),))

    def test_huge_verification_is_bounded(self):
        w=Word(KERNEL_C,2,())
        with self.assertRaisesRegex(ValueError,'limit'): verify_finite_win(w,10**30)


if __name__=='__main__': unittest.main()

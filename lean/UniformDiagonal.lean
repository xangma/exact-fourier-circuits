import UniformScalarPreparation
import OAI.Computability.FourierCircuit.RectStableAlgebra

set_option autoImplicit false

/- An explicit replacement for the finite-forbidden-set choice in the existing
   diagonal decomposition. Only prepared coefficients are conjugated. This is
   an algebraic/preparation component, not yet a schedule or RAM compiler. -/
namespace ExactFourierCircuits.UniformDiagonal
noncomputable section
open scoped BigOperators
open OAI.ExactFourier

variable {α : Type} [Fintype α]

def shift (c : α → ℂ) : ℂ := 1 + ∑ j, c j * starRingEnd ℂ (c j)

theorem shift_re (c : α → ℂ) :
    (shift c).re = 1 + ∑ j, ((c j).re ^ 2 + (c j).im ^ 2) := by
  simp only [shift, Complex.add_re, Complex.one_re, Complex.re_sum,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem shift_im (c : α → ℂ) : (shift c).im = 0 := by
  simp only [shift, Complex.add_im, Complex.one_im, Complex.im_sum,
    Complex.mul_im, Complex.conj_re, Complex.conj_im]
  simp only [mul_neg, mul_comm, neg_add_cancel, Finset.sum_const_zero, add_zero]

theorem shift_re_lower (c : α → ℂ) (j : α) :
    1 + (c j).re ^ 2 + (c j).im ^ 2 ≤ (shift c).re := by
  rw [shift_re]
  have h := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) =>
    add_nonneg (sq_nonneg (c i).re) (sq_nonneg (c i).im)) (Finset.mem_univ j)
  linarith

theorem shift_re_pos (c : α → ℂ) : 0 < (shift c).re := by
  rw [shift_re]
  have h : 0 ≤ ∑ j, ((c j).re ^ 2 + (c j).im ^ 2) :=
    Finset.sum_nonneg (fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  linarith

theorem shift_ne_zero (c : α → ℂ) : shift c ≠ 0 := by
  intro h
  have he := congrArg Complex.re h
  simp only [Complex.zero_re] at he
  linarith [shift_re_pos c]

theorem coefficient_sub_shift_ne_zero (c : α → ℂ) (j : α) : c j - shift c ≠ 0 := by
  intro h
  have he := congrArg Complex.re (sub_eq_zero.mp h)
  have hb := shift_re_lower c j
  nlinarith [sq_nonneg ((c j).re - 1 / 2), sq_nonneg (c j).im]

def first [DecidableEq α] (c : α → ℂ) : Matrix α α ℂ := Matrix.diagonal (fun j => c j - shift c)
def second [DecidableEq α] (c : α → ℂ) : Matrix α α ℂ := Matrix.diagonal (fun _ => shift c)

theorem split_diagonal [DecidableEq α] (c : α → ℂ) :
    first c + second c = Matrix.diagonal c := by
  ext i j
  by_cases h : i = j <;> simp [first, second, h]

theorem first_monomial [DecidableEq α] (c : α → ℂ) : MonomialMatrix (first c) :=
  MonomialMatrix.diagonal _ (coefficient_sub_shift_ne_zero c)

theorem second_monomial [DecidableEq α] (c : α → ℂ) : MonomialMatrix (second c) :=
  MonomialMatrix.diagonal _ (fun _ => shift_ne_zero c)

theorem diagonal_sumLayered [DecidableEq α] (c : α → ℂ) :
    SumLayered (Matrix.diagonal c) 1 2 := by
  rw [← split_diagonal c]
  exact (SumLayered.single (Layered.mono _ (first_monomial c))).add
    (SumLayered.single (Layered.mono _ (second_monomial c)))

open UniformScalarPreparation

/-- Same DAG at roots and inverse roots; no conjugation of array data. -/
def preparedShift {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (valid : d.Admissible roots) : ℂ :=
  1 + ∑ j, d.run roots valid j *
    d.run (fun j => starRingEnd ℂ (roots j)) ((d.admissible_conjugate roots).mpr valid) j

theorem preparedShift_eq {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (valid : d.Admissible roots) : preparedShift d roots valid = shift (d.run roots valid) := by
  unfold preparedShift shift
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [congrFun (d.run_conjugate roots valid) j]

theorem preparedShift_inverse_roots {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (valid : d.Admissible roots) :
    1 + ∑ j, d.run roots valid j *
      d.run (fun j => (roots j)⁻¹) ((d.admissible_inverse_roots roots unit).mpr valid) j =
        shift (d.run roots valid) := by
  unfold shift
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [congrFun (d.run_inverse_roots roots unit valid) j]

theorem preparedShift_ne_zero {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (valid : d.Admissible roots) : preparedShift d roots valid ≠ 0 := by
  rw [preparedShift_eq]
  exact shift_ne_zero _

theorem preparedCoefficient_sub_shift_ne_zero {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (valid : d.Admissible roots) (j : Fin a) :
    d.run roots valid j - preparedShift d roots valid ≠ 0 := by
  rw [preparedShift_eq]
  exact coefficient_sub_shift_ne_zero _ _

end
end ExactFourierCircuits.UniformDiagonal

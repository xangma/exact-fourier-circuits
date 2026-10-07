import Mathlib

/- New exact algebraic checks for the matrices emitted by src/exact_fourier/words.py. -/
namespace ExactFourierCircuits
noncomputable section

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

def a : ℂ := (1 + Complex.I) / 2
def b : ℂ := (1 - Complex.I) / 2
def C : Mat2 := !![a, b; b, a]
def swap : Mat2 := !![0, 1; 1, 0]
def diagonal (x y : ℂ) : Mat2 := !![x, 0; 0, y]
def S : Mat2 := diagonal 1 Complex.I
def H : Mat2 := !![1, 1; 1, -1]
def Hprime : Mat2 := a⁻¹ • (S * C * S)
def K : Mat2 := H * diagonal 2 1 * H * diagonal (-3) 1 * H
def D (t : ℂ) : Mat2 := diagonal (4 * t / 5) 1
def upperShear (t : ℂ) : Mat2 := !![1, t; 0, 1]

theorem C_square : C * C = swap := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [C, swap, a, b, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> simp [Complex.I_sq] <;> norm_num

lemma swap_square : swap * swap = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [swap, Matrix.mul_apply, Fin.sum_univ_two]

theorem C_inverse : C⁻¹ = swap * C := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, C_square, swap_square]

lemma S_C_S : S * C * S = a • H := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [S, diagonal, C, a, b, H, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> simp [Complex.I_sq] <;> norm_num <;> ring

lemma a_ne_zero : a ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  norm_num [a, Complex.div_re, Complex.normSq] at hr

theorem Hprime_eq_H : Hprime = H := by
  unfold Hprime
  rw [S_C_S, smul_smul, inv_mul_cancel₀ a_ne_zero, one_smul]

theorem K_formula : K = !![-8, -10; 0, -6] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [K, H, diagonal, Matrix.mul_apply, Fin.sum_univ_two]

lemma D_inverse (t : ℂ) (ht : t ≠ 0) :
    (D t)⁻¹ = diagonal (5 / (4 * t)) 1 := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D, diagonal, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp [ht]

theorem upper_shear_formula (t : ℂ) (ht : t ≠ 0) :
    upperShear t = D t * diagonal (-1 / 8) (-1 / 6) * K * (D t)⁻¹ := by
  rw [D_inverse t ht, K_formula]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [upperShear, D, diagonal, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp [ht]
  all_goals ring

end
end ExactFourierCircuits

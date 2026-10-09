import TypedKernelWords

/-!
Paper correspondence: An explicit power saving for the exact discrete Fourier
transform, OpenAI math revision adc7f1241b42e322a6451854ab7e4b4c146bf78a,
§3.4, equations (3.12)–(3.14), PDF pp. 17–18 (loc:three-kernel, loc:nonzero-shear, loc:nonzero-split).
The fixed pair order is (target, source). Every coefficient, including zero, uses two three-C blocks with proved nonzero scales; no complex zero test chooses the schedule.
-/

/-! The paper's fixed six-call compiler for an arbitrary prepared shear coefficient.
Conjugation is applied only to the coefficient, never to array inputs.  This module
does not yet construct the coefficient's arithmetic DAG or its conjugate DAG. -/
namespace ExactFourierCircuits.UniformLocalShear
noncomputable section
open OAI.ExactFourier TypedKernelWords

/- Paper: Equation (3.14), p. 18 (loc:nonzero-split): kappa and mu-kappa are both nonzero for every complex coefficient. -/
def kappa (mu : ℂ) : ℂ := 1 + mu * starRingEnd ℂ mu

theorem kappa_re (mu : ℂ) :
    (kappa mu).re = 1 + mu.re ^ 2 + mu.im ^ 2 := by
  simp only [kappa, Complex.add_re, Complex.one_re, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

theorem kappa_im (mu : ℂ) : (kappa mu).im = 0 := by
  simp only [kappa, Complex.add_im, Complex.one_im, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem kappa_re_pos (mu : ℂ) : 0 < (kappa mu).re := by
  rw [kappa_re]
  nlinarith [sq_nonneg mu.re, sq_nonneg mu.im]

theorem kappa_ne_zero (mu : ℂ) : kappa mu ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp only [Complex.zero_re] at hr
  linarith [kappa_re_pos mu]

theorem second_ne_zero (mu : ℂ) : mu - kappa mu ≠ 0 := by
  intro h
  have hr := congrArg Complex.re (sub_eq_zero.mp h)
  rw [kappa_re] at hr
  nlinarith [sq_nonneg (mu.re - 1 / 2), sq_nonneg mu.im]

theorem split_sum (mu : ℂ) : kappa mu + (mu - kappa mu) = mu := by ring

theorem upperShear_mul (x y : ℂ) :
    upperShear x * upperShear y = upperShear (x + y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperShear, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- Always the same two three-call blocks; no test of `mu = 0` occurs. -/
/- Paper: Equations (3.12)–(3.14), pp. 17–18: concatenate two three-forward-C blocks. This is an algebraic word; shared preparation is supplied later. -/
def word (mu : ℂ) : List Step :=
  shearWord (kappa mu) (kappa_ne_zero mu) ++
    shearWord (mu - kappa mu) (second_ne_zero mu)

theorem word_matrix (mu : ℂ) : wordMatrix (word mu) = upperShear mu := by
  rw [word, wordMatrix_append, shearWord_matrix, shearWord_matrix, upperShear_mul]
  rw [add_comm, split_sum]

theorem word_calls (mu : ℂ) : wordCalls (word mu) = 6 := by
  simp only [word, wordCalls_append, shearWord_calls]

theorem word_action (mu : ℂ) (x : Fin 2 → ℂ) :
    (wordMatrix (word mu)).mulVec x 0 = x 0 + mu * x 1 ∧
    (wordMatrix (word mu)).mulVec x 1 = x 1 := by
  rw [word_matrix]
  simp [upperShear, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem compile_shear (mu : ℂ) :
    ∃ W : List (WordStep C2 2), wordMatrix W = upperShear mu ∧ wordCalls W = 6 :=
  ⟨word mu, word_matrix mu, word_calls mu⟩

theorem zero_matrix : wordMatrix (word 0) = 1 := by
  rw [word_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperShear]

theorem zero_calls : wordCalls (word 0) = 6 := word_calls 0

end
end ExactFourierCircuits.UniformLocalShear

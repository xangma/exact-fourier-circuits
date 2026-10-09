import UniformRoots

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.3 (5.7), PDF p.22, and the chirp-ratio preparation
paragraph, PDF p.23 (`eq:chirp`).

Exact positive-sign chirp identity and the geometric-ratio recurrences.
These are algebraic facts; the table machine supplies their charged execution.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformChirp
open OAI.ExactFourier
open scoped BigOperators
noncomputable section

/- Paper stage: §5.3 (5.7), PDF p.22 (`eq:chirp`): the signed quadratic-exponent identity fixes the positive DFT convention. -/
theorem chirp_exponents (j k : ℤ) : j ^ 2 - (k - j) ^ 2 + k ^ 2 = 2 * (j * k) := by ring

theorem chirp_identity (eta : ℂ) (heta : eta ≠ 0) (j k : ℤ) :
    eta ^ (j ^ 2) * eta ^ (-(k - j) ^ 2) * eta ^ (k ^ 2) = eta ^ (2 * (j * k)) := by
  rw [← zpow_add₀ heta, ← zpow_add₀ heta]
  congr 1
  ring

/-- The specified half-angle root supplies the ordinary positive-exponent DFT. -/
theorem specified_chirp (n j k : ℕ) (hn : 0 < n) :
    zeta n ^ (j * k) = zeta (2 * n) ^ ((j : ℤ) ^ 2) *
      zeta (2 * n) ^ (-((k : ℤ) - (j : ℤ)) ^ 2) * zeta (2 * n) ^ ((k : ℤ) ^ 2) := by
  rw [chirp_identity _ (UniformRoots.specifiedRoot_ne_zero _) ]
  have hroot : zeta (2 * n) ^ 2 = zeta n := by
    simpa only [mul_comm] using UniformRoots.specifiedRoot_mul_power n 2 hn (by omega)
  rw [← hroot, ← pow_mul]
  have he : 2 * ((j : ℤ) * (k : ℤ)) = ((2 * (j * k) : ℕ) : ℤ) := by push_cast; ring
  rw [he, zpow_natCast]

/-- Exact chirp factorization before the separate cyclic-padding implementation. -/
/- Paper stage: §5.3, operand construction following (5.7), PDF p.22: the identity is summed over every input coordinate. -/
theorem fourier_chirp_sum (n : ℕ) (hn : 0 < n) (x : Fin n → ℂ) (k : Fin n) :
    (fourierMatrix n).mulVec x k =
      zeta (2 * n) ^ ((k.val : ℤ) ^ 2) *
        ∑ j : Fin n, zeta (2 * n) ^ (-((k.val : ℤ) - (j.val : ℤ)) ^ 2) *
          zeta (2 * n) ^ ((j.val : ℤ) ^ 2) * x j := by
  simp only [Matrix.mulVec, dotProduct, fourierMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.mul_comm k.val j.val, specified_chirp n j.val k.val hn]
  ring

/- Paper stage: §5.3, linear chirp preparation, PDF p.23: update both chirp and geometric ratio instead of repeated long exponentiation. -/
def chirp (eta : ℂ) (j : ℕ) : ℂ := eta ^ (j ^ 2)
def ratio (eta : ℂ) (j : ℕ) : ℂ := eta ^ (2 * j + 1)

theorem chirp_zero (eta : ℂ) : chirp eta 0 = 1 := by simp [chirp]
theorem ratio_zero (eta : ℂ) : ratio eta 0 = eta := by simp [ratio]

/-- One multiplication generates each successive chirp once its ratio is available. -/
theorem chirp_succ (eta : ℂ) (j : ℕ) : chirp eta (j + 1) = chirp eta j * ratio eta j := by
  unfold chirp ratio
  rw [← pow_add]
  congr 1
  ring

/-- A second multiplication updates the ratio, without separate long powering. -/
theorem ratio_succ (eta : ℂ) (j : ℕ) : ratio eta (j + 1) = ratio eta j * eta ^ 2 := by
  unfold ratio
  rw [← pow_add]
  congr 1

theorem chirp_ne_zero (eta : ℂ) (heta : eta ≠ 0) (j : ℕ) : chirp eta j ≠ 0 :=
  pow_ne_zero _ heta

end
end ExactFourierCircuits.UniformChirp

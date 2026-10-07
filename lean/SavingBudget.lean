import Mathlib

/- Arithmetic consequences of the proposed count formula. The formula still
   needs to be proved for an actual word; these lemmas do not supply one. -/
namespace ExactFourierCircuits.SavingBudget

/-- Cancelling the common ordinary-transform contribution isolates the margin. -/
theorem coefficient_saving {S Δ W m f r H : ℕ}
    (hbalance : S + Δ = W * m) :
    S * f + r * W + 2 * H < (m * f + r) * W ↔ 2 * H < Δ * f := by
  have he : (m * f + r) * W = S * f + Δ * f + r * W := by
    calc
      (m * f + r) * W = (W * m) * f + r * W := by ring
      _ = (S + Δ) * f + r * W := by rw [hbalance]
      _ = S * f + Δ * f + r * W := by ring
  rw [he]
  omega

/-- A symbolic common positive factor can be retained without expanding it. -/
theorem factored_saving {S Δ W m f r H t : ℕ}
    (hbalance : S + Δ = W * m) (ht : 0 < t) (hmargin : 2 * H < Δ * f) :
    (S * f + r * W + 2 * H) * t < ((m * f + r) * W) * t := by
  exact Nat.mul_lt_mul_of_pos_right ((coefficient_saving hbalance).mpr hmargin) ht

/-- The least integer strictly above the budget-to-margin ratio suffices. -/
theorem floor_choice_saves {Δ H : ℕ} (hΔ : 0 < Δ) :
    2 * H < Δ * (2 * H / Δ + 1) := by
  have hmod := Nat.mod_lt (2 * H) hΔ
  have he := Nat.mod_add_div (2 * H) Δ
  have hmul : Δ * (2 * H / Δ + 1) = Δ * (2 * H / Δ) + Δ := by ring
  rw [hmul]
  omega

/-- Prove exponent regrouping with symbolic exponents before choosing enormous sizes. -/
theorem tensor_axis_factorization (n r : ℕ) (hn : 0 < n) :
    (n + r) * 2 ^ (n + r - 1) = ((n + r) * 2 ^ r) * 2 ^ (n - 1) := by
  have he : n + r - 1 = r + (n - 1) := by omega
  rw [he, pow_add]
  exact (Nat.mul_assoc _ _ _).symm

end ExactFourierCircuits.SavingBudget

import KernelIdentities
import OAI.Computability.FourierCircuit.Main

/- The exact interface a constructed word must satisfy. These theorems do not
   supply that word or certify the Python network. -/
namespace ExactFourierCircuits.ConstructiveBridge
noncomputable section
open ExactFourierCircuits

lemma b_ne_zero : ExactFourierCircuits.b ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  norm_num [ExactFourierCircuits.b, Complex.div_re, Complex.normSq] at hr

theorem kernel_isUnit : IsUnit C := by
  refine ⟨⟨C, swap * C, ?_, ?_⟩, rfl⟩
  · calc
      C * (swap * C) = (C * C) * (C * C) := by
        rw [← C_square]
        simp only [mul_assoc]
      _ = 1 := by rw [C_square, swap_square]
  · rw [mul_assoc, C_square, swap_square]

theorem kernel_not_isMonomial : ¬ OAI.ExactFourier.IsMonomial C := by
  rintro ⟨σ, d, _, h⟩
  by_cases hs : σ 0 = 0
  · have hz : C 1 0 = 0 := by
      rw [h]
      simp [hs]
    exact b_ne_zero (by simpa [C] using hz)
  · have hz : C 0 0 = 0 := by
      rw [h]
      simp [Ne.symm hs]
    exact a_ne_zero (by simpa [C] using hz)

/-- Correctness and strict call saving must refer to the same literal word. -/
theorem finiteWin_of_word {b : ℕ} (hb : 2 ≤ b)
    (W : List (OAI.ExactFourier.WordStep C (2 ^ b)))
    (hW : OAI.ExactFourier.wordMatrix W = OAI.ExactFourier.tensorPower C b)
    (hcost : OAI.ExactFourier.wordCalls W < b * 2 ^ (b - 1)) :
    OAI.ExactFourier.FiniteWinStatement :=
  ⟨2, C, kernel_isUnit, kernel_not_isMonomial, b, hb, W, hW, hcost⟩

/-- The existing transfer charges scalar gates, including diagonal scalings. -/
theorem main_of_word {b : ℕ} (hb : 2 ≤ b)
    (W : List (OAI.ExactFourier.WordStep C (2 ^ b)))
    (hW : OAI.ExactFourier.wordMatrix W = OAI.ExactFourier.tensorPower C b)
    (hcost : OAI.ExactFourier.wordCalls W < b * 2 ^ (b - 1)) :
    OAI.ExactFourier.MainStatement :=
  OAI.ExactFourier.win_to_fourier (finiteWin_of_word hb W hW hcost)

end
end ExactFourierCircuits.ConstructiveBridge

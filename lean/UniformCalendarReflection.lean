import UniformFourierCalendarEpoch
import UniformAllAxisCalendarTensor

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarReflection
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformLayerRestriction
open UniformCalendarRenderTick

/-- Transposition retains the actual cached diagonal and ordered C instruction. -/
theorem step_fixed {n : ℕ} (s : WordStep C n) (hs : StepRestricted s) :
    (UniformLocalFourierWord.transposeStep s).matrix=s.matrix := by
  cases s with
  | monomial M hM =>
    obtain ⟨d,rfl⟩ := hs
    simp only [UniformLocalFourierWord.transposeStep,WordStep.matrix,Matrix.diagonal_transpose]
  | call e => rfl

/-- Arbitrary mixed parallel phases remain symmetric individually. -/
theorem layer_fixed {n : ℕ} (L : Layer n) (hL : Restricted L) :
    L.transpose.matrix=L.matrix := by
  induction L with
  | step s => simpa only [Layer.transpose,Layer.step_matrix] using step_fixed s hL
  | parallel e L R ihL ihR =>
    simp only [Layer.transpose,Layer.parallel_matrix,ihL hL.1,ihR hL.2]
  | embed e L ih => simp only [Layer.transpose,Layer.embed_matrix,ih hL]
  | batch position steps =>
    simp only [Layer.transpose,Layer.batch_matrix]
    congr 2
    funext i
    exact step_fixed (steps i) (hL i)

theorem layer_symmetric {n : ℕ} (L : Layer n) (hL : Restricted L) :
    L.matrix.transpose=L.matrix := by
  rw [←Layer.transpose_matrix]
  exact layer_fixed L hL

theorem tick_symmetric {n : ℕ} (L : List (Layer n)) (hL : ScheduleRestricted L) (t : ℕ) :
    (tick L t).transpose=tick L t := by
  by_cases ht:t<L.length
  · rw [tick_of_lt _ _ ht]
    exact layer_symmetric _ (hL _ (List.get_mem _ _))
  · rw [tick_of_le L t (Nat.le_of_not_gt ht),Matrix.transpose_one]

/-- Reflect time only: the same cached ordered calls and factor lanes implement
the literal transposed schedule. No swapped endpoint cache is required. -/
theorem transpose_tick {n : ℕ} (L : List (Layer n)) (hL : ScheduleRestricted L)
    (t : ℕ) (ht:t<L.length) :
    tick (transpose L) t=tick L (L.length-1-t) := by
  rw [UniformFourierCalendarEpoch.tick_transpose _ _ ht,tick_symmetric L hL]

theorem reflected_forward_snapshot {n : ℕ} (P : UniformBalancedToeplitz.Plan n)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) (t : ℕ)
    (ht:t<(render P f hf).length) :
    (UniformAllAxisCalendarTensor.axisSnapshot P f hf ((render P f hf).length-1-t)).matrix=
      tick (transpose (render P f hf)) t := by
  rw [UniformAllAxisCalendarTensor.axisSnapshot_matrix]
  exact (transpose_tick _ (render_restricted P f hf) t ht).symm

theorem transpose_epoch {n : ℕ} (left right d : Fin n→ℂ)
    (hl : ∀i,left i≠0) (hr : ∀i,right i≠0) (hd : ∀i,d i≠0)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0)
    (t : ℕ) (ht:t<(toeplitz n f hf).length) :
    tick (symmetric (sandwich left right hl hr f hf) d hd) (1+t)=
      tick (toeplitz n f hf) ((toeplitz n f hf).length-1-t) := by
  rw [UniformFourierCalendarEpoch.transpose_epoch _ _ _ _ _ _ _ _ t ht]
  exact tick_symmetric _ (render_restricted _ f hf) _

end
end ExactFourierCircuits.UniformCalendarReflection

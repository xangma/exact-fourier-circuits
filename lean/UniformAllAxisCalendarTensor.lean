import UniformFourierCalendarEpoch
import UniformSynchronizedLayers

set_option autoImplicit false
namespace ExactFourierCircuits.UniformAllAxisCalendarTensor
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformCalendarRenderTick
open UniformLayerSnapshot UniformCalendarRenderSnapshot UniformGlobalCalendarUnion
open UniformBalancedToeplitz UniformSynchronizedLayers

theorem slot_tick {r T : ℕ} (L : List (Layer r)) (h : L.length≤T) (t : Fin T) :
    (slot L h t).matrix = tick L t.val := by
  change ((padded T L).get _).matrix=_
  have idx : Fin.cast (padded_length L h).symm t = ⟨t.val,by rw [padded_length L h];exact t.isLt⟩ := Fin.ext rfl
  rw [idx]
  rw [←tick_of_lt (padded T L) t.val (by rw [padded_length L h];exact t.isLt)]
  rw [padded,tick_append]
  by_cases ht : t.val<L.length
  · rw [ite_eq_left ht]
  · rw [ite_eq_right ht,tick_of_le L t.val (Nat.le_of_not_gt ht)]
    have z : t.val-L.length < T-L.length := by omega
    have z' : t.val-L.length < (List.replicate (T-L.length) (Layer.idle r)).length := by simpa using z
    simp [tick,List.getElem?_eq_getElem z']

def axisSnapshot {r : ℕ} (P : Plan r) (f : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f≠0) (t : ℕ) : Snapshot (Fin r) :=
  treeSnapshot P 0 0 t r (by omega) (renderFamily P 0 0 t f hf)

theorem axisSnapshot_matrix {r : ℕ} (P : Plan r) (f : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f≠0) (t : ℕ) :
    (axisSnapshot P f hf t).matrix = tick (UniformLocalFourierLayers.render P f hf) t := by
  rw [axisSnapshot,treeSnapshot_renderFamily]
  simp only [Nat.zero_le,↓reduceIte,Nat.sub_zero]
  have e : rootEmbedding r 0 r (by omega) = (Equiv.refl (Fin r)).toEmbedding := by
    ext i
    change 0+i.val=i.val
    omega
  rw [e,Embedded.matrix_equiv]
  rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι] {r : ι→ℕ} {T : ℕ}

omit [DecidableEq ι] in
/-- All axes use their own actual active tree family at the same global tick.
No compiler-phase alignment across axes or parallel subtrees is required. -/
theorem tensor_calendar (P : ∀i,Plan (r i)) (f : ∀_i : ι,PowerSeries ℂ)
    (hf : ∀i,PowerSeries.constantCoeff (f i)≠0)
    (h : ∀i,(UniformLocalFourierLayers.render (P i) (f i) (hf i)).length≤T) (t : Fin T) :
    PiTensor.matrix (fun i => (axisSnapshot (P i) (f i) (hf i) t.val).matrix) =
      tensorSlot (fun i => UniformLocalFourierLayers.render (P i) (f i) (hf i)) h t := by
  apply congrArg PiTensor.matrix
  funext i
  rw [axisSnapshot_matrix,slot_tick]

/-- The synchronized tree calendars have the exact tensor endpoint of the
actual rendered Toeplitz schedules. This does not identify one tree with a DFT. -/
theorem tensor_calendar_product (P : ∀i,Plan (r i)) (f : ∀_i : ι,PowerSeries ℂ)
    (hf : ∀i,PowerSeries.constantCoeff (f i)≠0)
    (h : ∀i,(UniformLocalFourierLayers.render (P i) (f i) (hf i)).length≤T) :
    (List.ofFn (fun t : Fin T => PiTensor.matrix
      (fun i => (axisSnapshot (P i) (f i) (hf i) t.val).matrix))).reverse.prod =
      PiTensor.matrix (fun i => matrix (UniformLocalFourierLayers.render (P i) (f i) (hf i))) := by
  simp_rw [tensor_calendar P f hf h]
  exact tensorSchedule_product _ h

end
end ExactFourierCircuits.UniformAllAxisCalendarTensor

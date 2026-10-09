import UniformGlobalCalendarUnion
import UniformGlobalCalendarMatchingPhase

set_option autoImplicit false

namespace ExactFourierCircuits.UniformCalendarRenderTick
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers

/-- A literal rendered layer, with the paper's identity padding after its end. -/
def tick {n : ℕ} (L : List (Layer n)) (t : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  ((L[t]?).getD (Layer.idle n)).matrix

@[simp] theorem tick_nil (n t : ℕ) : tick ([] : List (Layer n)) t = 1 := by
  simp [tick]

@[simp] theorem tick_cons_zero {n : ℕ} (l : Layer n) (L : List (Layer n)) :
    tick (l :: L) 0 = l.matrix := rfl

@[simp] theorem tick_cons_succ {n : ℕ} (l : Layer n) (L : List (Layer n)) (t : ℕ) :
    tick (l :: L) (t + 1) = tick L t := rfl

theorem tick_of_lt {n : ℕ} (L : List (Layer n)) (t : ℕ) (h : t < L.length) :
    tick L t = (L.get ⟨t,h⟩).matrix := by
  simp [tick,List.getElem?_eq_getElem h]

theorem tick_of_le {n : ℕ} (L : List (Layer n)) (t : ℕ) (h : L.length ≤ t) :
    tick L t = 1 := by
  simp [tick,List.getElem?_eq_none h]

theorem tick_append {n : ℕ} (L R : List (Layer n)) (t : ℕ) :
    tick (L ++ R) t = if t < L.length then tick L t else tick R (t - L.length) := by
  by_cases h : t < L.length
  · simp only [ite_eq_left h,tick,List.getElem?_append_left h]
  · simp only [ite_eq_right h,tick,List.getElem?_append_right (Nat.le_of_not_gt h)]

theorem tick_embed {a n : ℕ} (e : Fin a ↪ Fin n) (L : List (Layer a)) (t : ℕ) :
    tick (L.map (Layer.embed e)) t = Embedded.matrix e (tick L t) := by
  by_cases h : t < L.length
  · rw [tick_of_lt _ t (by simpa using h),tick_of_lt _ t h]
    simp only [List.get_eq_getElem,List.getElem_map,Layer.embed_matrix]
  · rw [tick_of_le _ t (by simpa using Nat.le_of_not_gt h),
      tick_of_le _ t (Nat.le_of_not_gt h),Embedded.matrix_one]

/-- This pointwise statement allows children to be at unrelated local phases. -/
theorem tick_parallel {a b n : ℕ} (e : (Fin a ⊕ Fin b) ≃ Fin n)
    (L : List (Layer a)) (R : List (Layer b)) (t : ℕ) :
    tick (parallel e L R) t =
      Matrix.reindex e e (Matrix.fromBlocks (tick L t) 0 0 (tick R t)) := by
  induction L generalizing R t with
  | nil =>
    induction R generalizing t with
    | nil => simp [parallel]
    | cons r R ih =>
      cases t with
      | zero => simp [parallel]
      | succ t => simpa only [parallel,tick_cons_succ,tick_nil] using ih t
  | cons l L ih =>
    cases R with
    | nil =>
      cases t with
      | zero => simp [parallel]
      | succ t => simpa only [parallel,tick_cons_succ,tick_nil] using ih [] t
    | cons r R =>
      cases t with
      | zero => simp [parallel]
      | succ t => simpa only [parallel,tick_cons_succ] using ih R t

end
end ExactFourierCircuits.UniformCalendarRenderTick

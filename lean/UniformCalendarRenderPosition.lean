import UniformCalendarRenderPlan

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarRenderPosition
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformBalancedToeplitz UniformWorkspacePlanner
open UniformLocalCacheTiming UniformLocalCacheTreeMachine UniformLocalRectangleDescriptors
open UniformGlobalCalendarGeometry UniformGlobalCalendarUnion
open UniformCalendarRenderPieces UniformCalendarRenderPlan

theorem left_val (v : ℕ) (i : Fin (v/2)) : (left v i).val = i.val := rfl
theorem right_val (v : ℕ) (i : Fin (v-v/2)) : (right v i).val = v/2+i.val := rfl

def Positioned {n : ℕ} (o : ℕ) (p : Piece n) : Prop :=
  ∀ i, o+(p.position i).val = UniformGlobalCalendarGeometry.Event.low p.descriptor.event+i.val

theorem stamp_positioned {n : ℕ} (o start : ℕ) (L : List (Piece n))
    (h : ∀ p∈L,Positioned o p) : ∀ p∈stamp start L,Positioned o p := by
  induction L generalizing start with
  | nil => simp [stamp]
  | cons p L ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h p (by simp)
    · exact ih _ (fun x hx => h x (by simp [hx])) q hq

theorem correction_positioned (v : ℕ) (hv : 0<selected v) (o start : ℕ) (f : PowerSeries ℂ) :
    ∀ p∈correctionPieces v hv o start f,Positioned o p := by
  apply stamp_positioned
  intro p hp
  obtain ⟨q,_hq,rfl⟩ := List.mem_map.mp hp
  intro i
  rfl

theorem calendar_positioned {v : ℕ} (P : Plan v) (o start : ℕ)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) :
    ∀ p∈calendar P o start f hf,Positioned o p := by
  induction P generalizing o start with
  | direct v cap =>
    intro p hp
    have eq : p=(directPiece v cap o f hf).withStart start := List.mem_singleton.mp hp
    subst p
    intro i
    rfl
  | split v hn hv L R ihL ihR =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
        intro i
        change o+(left v (q.position i)).val=_
        rw [left_val]
        exact ihL o start q hq i
      · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
        intro i
        change o+(right v (q.position i)).val=_
        rw [right_val]
        have h:=ihR (o+v/2) start q hq i
        simpa only [Nat.add_assoc,Piece.embed] using h
    · exact correction_positioned v hv o _ f p hp

end
end ExactFourierCircuits.UniformCalendarRenderPosition

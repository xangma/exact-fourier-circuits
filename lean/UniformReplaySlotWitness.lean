import UniformReplaySlotIndex

set_option autoImplicit false
namespace ExactFourierCircuits.UniformReplaySlotWitness
noncomputable section
open UniformLocalCacheChronology UniformLocalReplayAssembly UniformReplaySlotIndex
open UniformLocalCacheSlotConductorMachine (SlotWitness)

lemma bound {K j : ℕ} {slot : Slot} (h : SlotWitness K j slot) :
    j < (replaySlots (8*K+6)).length := by
  rcases h with ⟨p,t,rfl,ht,_⟩
  rw [replaySlots_length]
  have before := prefix_mono (8*K+6) (show p.val+1≤6 by have:=p.isLt; omega)
  rw [prefix_next, prefix_total] at before
  omega

/-- Literal phase/depth/color decoding is exactly the normal replay ordinal. -/
lemma get {K j : ℕ} {slot : Slot} (h : SlotWitness K j slot)
    (hj : j < (replaySlots (8*K+6)).length) :
    (replaySlots (8*K+6)).get ⟨j,hj⟩ = slot := by
  rcases h with ⟨p,t,rfl,ht,rfl⟩
  exact replay_get_phase (8*K+6) p t ht

lemma depth_color {K j : ℕ} {slot : Slot} (h : SlotWitness K j slot) :
    slot.depth ≤ 8*K+6 ∧ slot.color < 11 := by
  rcases h with ⟨p,t,_,ht,rfl⟩
  have color : t%11<11 := Nat.mod_lt _ (by omega)
  have dep : t/11<UniformLocalReplaySlotMachine.levelCount (8*K+6) (flags p).broadcast := by
    change t<11*UniformLocalReplaySlotMachine.levelCount (8*K+6) (flags p).broadcast at ht
    omega
  cases b : (flags p).broadcast <;> cases inv : (flags p).inverse <;>
    simp [UniformLocalReplaySlotMachine.decodedSlot, b, inv,
      UniformLocalReplaySlotMachine.levelCount] at * <;> omega

lemma layer_bound {r n a K j : ℕ} (D : UniformToeplitzCrossDAG.DAG r n a)
    {slot : Slot} (h : SlotWitness K j slot) : j<(UniformDAGLayers.replayLayers D (8*K+6) 6).length := by
  rw [← replaySlots_layers D (8*K+6), List.length_map]
  exact bound h

/-- The actual cached slot evaluates to the actual normal replay layer at that
ordinal, including the physically reversed inverse depths and colors. -/
lemma layer_get {r n a K j : ℕ} (D : UniformToeplitzCrossDAG.DAG r n a)
    {slot : Slot} (h : SlotWitness K j slot)
    (hj : j<(UniformDAGLayers.replayLayers D (8*K+6) 6).length) :
    (UniformDAGLayers.replayLayers D (8*K+6) 6).get ⟨j,hj⟩ = layer D (8*K+6) slot := by
  simp only [List.get_eq_getElem]
  rw [List.getElem_of_eq (replaySlots_layers D (8*K+6)).symm, List.getElem_map]
  exact congrArg (layer D (8*K+6)) (get h (bound h))

end
end ExactFourierCircuits.UniformReplaySlotWitness

import DFTModelGlobalKernelSourceCells
set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalKernelSource
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (setPC)
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAdmissibilityControl DFTModelAffine
noncomputable section

/-- Every real sector's closed typed saving bill, including its charged typed
gather/setup, is paid by the SAME complete original kernel witness. The actual
all-gather time was derived from the literal372 constructor, not supplied. -/
theorem Result.saving_work {F n i K prepTicks loopTicks returnTicks : ℕ} (c : Context F)
 {v v0 : ℕ→Fin c.packing.volume→Scalar} {x : Fin n→ℂ} {s s0 a a0 t t0 z z0 : State} {trace : List ℕ}
 (h : Result (i:=i) c v v0 K x s s0 a a0 t t0 z z0 prepTicks loopTicks returnTicks trace)
 (bank : Tape Tagged.T)
 (encoded : DFTModelGlobalSectorLoop.Encoded c.loop.volume bank
  (UniformConditionalKernelLayout.packed c v) (UniformConditionalKernelLayout.packed c v0)) :
 ((states c).map (DFTModelGlobalSectorLoop.savingBill c.loop.volume bank)).sum≤
  (K+11)*(prepTicks+(loopTicks+(returnTicks+1)+1)) := by
 have charged:=h.children.saving_work bank encoded (sector_fits c)
 have costs : (states c).map DFTModelGlobalSectorLoop.gatherTicks=
  (states c).map (fun st=>W*(7*st.width+12)+17) := by
  apply List.map_congr_left
  intro st hs
  obtain ⟨j,hj,eq⟩:=List.getElem_of_mem hs
  subst st
  simp only[DFTModelGlobalSectorLoop.gatherTicks,c.loop.pow j hj]
 have lower : ((states c).map DFTModelGlobalSectorLoop.gatherTicks).sum≤prepTicks := by
  rw[costs]
  exact h.gathers
 exact charged.trans (Nat.mul_le_mul_left (K+11) (by omega))

theorem Result.matched {F n i K prepTicks loopTicks returnTicks : ℕ} (c : Context F)
 {v v0 : ℕ→Fin c.packing.volume→Scalar} {x : Fin n→ℂ} {s s0 a a0 t t0 z z0 : State} {trace : List ℕ}
 (h : Result (i:=i) c v v0 K x s s0 a a0 t t0 z z0 prepTicks loopTicks returnTicks trace) :
 StateMatch (setPC z (child.length+613)) (setPC z0 (child.length+613)) := h.returned.matched.withPC _

theorem Result.outputs {F n i K prepTicks loopTicks returnTicks : ℕ} (c : Context F)
 {v v0 : ℕ→Fin c.packing.volume→Scalar} {x : Fin n→ℂ} {s s0 a a0 t t0 z z0 : State} {trace : List ℕ}
 (h : Result (i:=i) c v v0 K x s s0 a a0 t t0 z z0 prepTicks loopTicks returnTicks trace) :
 z.outputs=s.outputs ∧z0.outputs=s0.outputs ∧z.rootOrders=s.rootOrders ∧z0.rootOrders=s0.rootOrders :=
 ⟨h.returned.outputs.trans (h.children.frame.outputs.trans h.preparation.actual.outputs),
  h.returned.outputs0.trans (h.children.frame.outputs0.trans h.preparation.baseline.outputs),
  h.returned.roots.trans (h.children.frame.roots.trans h.preparation.actual.roots),
  h.returned.roots0.trans (h.children.frame.roots0.trans h.preparation.baseline.roots)⟩

theorem Result.once_per_sector {F n i K prepTicks loopTicks returnTicks : ℕ} (c : Context F)
 {v v0 : ℕ→Fin c.packing.volume→Scalar} {x : Fin n→ℂ} {s s0 a a0 t t0 z z0 : State} {trace : List ℕ}
 (h : Result (i:=i) c v v0 K x s s0 a a0 t t0 z z0 prepTicks loopTicks returnTicks trace) :
 trace.length=(states c).length ∧loopTicks=trace.sum+12*(states c).length+9 :=
 ⟨h.children.calls,h.children.exactTicks⟩

end
end ExactFourierCircuits.DFTModelGlobalKernelSource

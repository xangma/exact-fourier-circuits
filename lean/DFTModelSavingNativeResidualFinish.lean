import DFTModelSavingNativeResidualEntry

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeResidual
open UniformMachine BinaryFrames DFTModelAdmissibilityControl
open UniformRecursiveResidualEdge (Parent parent_frame parent_direction)
noncomputable section
attribute [local irreducible] P.program

structure FinishResult (n B k q A F T r stack depth index dim finish flag:ℕ)
 (x:Fin n→ℂ)(s u:State):Prop where
 run:BoundedRuns P.program n x B s 6 u
 pc:u.pc=P.address .loop
 parent:Parent k q A F finish r stack depth u
 frame:UniformRecursiveResidualControl.Frame F s u

theorem finish (n B k q A F T r stack depth index dim stop flag:ℕ)
 (x:Fin n→ℂ)(s:State)(pc:s.pc=P.address .edgeDone)
 (h:UniformRecursiveResidualDirection.Control k q A F T r stack depth index dim stop flag s)
 (mode:s.natHeap (F-6)=some 0)(bound:WordBound B s)(code:P.program.length≤B):
 ∃u,FinishResult n B k q A F T r stack depth index dim stop flag x s u:=by
 obtain ⟨c,run,cp,ce,cn,ef⟩:=UniformRecursiveResidualControlJoin.edge_done_finish n B F 0 x s pc h.one h.frontier mode bound code
 have cpc:c.pc=P.address .recordAdvance:=by simpa only [Nat.zero_lt_one,ite_true] using cp
 have cone:c.natReg 4153=1:=(ef.natReg _ (by unfold UniformRecursiveResidualControl.Changed;omega)).trans h.one
 have cfinish:c.natReg 4130=stop:=ce.trans h.finish
 obtain ⟨u,advance,up,ptr,un,af⟩:=UniformRecursiveResidualControl.record_advance n B F stop x c
  cpc cone cfinish run.final_bound code
 have fr:=ef.trans af
 exact ⟨u,run.trans advance,up,parent_frame (parent_direction h) fr ptr,fr⟩

end
end ExactFourierCircuits.DFTModelSavingNativeResidual

import UniformPreparedKernelExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformPreparedKernelTags
open UniformMachine
open UniformConditionalKernelLayout (Context Ready packed movementCost programFor)
noncomputable section

/-- Prepared tags survive all charged physical movements around the actual
common-C loop. Only its explicitly internal prepared-root obligation remains. -/
theorem execution {W F R n ordinal:ℕ} (child:Program) (c:Context W F R)
 (cost:ℕ→ℕ) (v:ℕ→Fin c.packing.volume→Scalar) (x:Fin n→ℂ) (s:State)
 (ready:Ready c ordinal v s) (hi:ordinal<(UniformProducedSectorChildABI.states c.physical).length)
 (root:UniformPreparedSectorLoop.RootBody child W n c.inverse.layout.B F R cost x)
 (prepared:∀r,r<W→∀j:Fin c.packing.volume,(v r j).dependent=false)
 (positive:0<W) (code:child.length+614≤c.metadata.B) (pc:s.pc=0) (wb:WordBound c.metadata.B s):
 ∃u ticks,BoundedExecution (programFor child W) n x c.metadata.B s ticks u ∧
 ticks ≤ movementCost c+UniformConditionalSectorLoop.budget cost (UniformProducedSectorChildABI.states c.physical)+
  213*c.inverse.layout.total+W*(16*c.inverse.layout.total+12)+
  (12*W+20)*(UniformProducedSectorChildABI.states c.physical).length+57 ∧u.pc=child.length+613 ∧
 (∀r,r<W→∀j:Fin (UniformSectorPackingMachine.physicalVolume c.physical),
  (u.scalarHeap (c.inverse.destination+r*UniformSectorPackingMachine.physicalVolume c.physical+j.val)).map Scalar.dependent=
   some false) ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders:=by
 obtain ⟨mid,u,ticks,done,run,cheap,up,stored,outputs,roots⟩:=
  UniformPreparedKernelExecution.execution child c cost v x s ready hi root prepared positive code pc wb
 refine ⟨u,ticks,run,cheap,up,?_,outputs,roots⟩
 intro r hr j
 have vol:UniformSectorPackingMachine.physicalVolume c.physical=c.inverse.layout.total:=
  c.physicalVolume.trans c.inverseVolume
 have actual:=stored r hr (finCongr vol j)
 have address:(c.inverse.destination+r*c.inverse.layout.total+(finCongr vol j).val)=
  c.inverse.destination+r*UniformSectorPackingMachine.physicalVolume c.physical+j.val:=by simp only[finCongr_apply,Fin.val_cast,vol]
 rw[address] at actual
 rw[actual]
 apply congrArg some
 let cover:=UniformPreparedPayloadBridge.actual_cover c.physical c.loop.volume
  ((c.physicalVolume.trans c.inverseVolume).trans c.loopVolume.symm)
 let k:Fin c.loop.volume:=finCongr c.loopVolume.symm
  ((UniformSectorPackingMachine.physicalUnpacking c.physical c.inverse.layout vol).symm (finCongr vol j))
 exact UniformPreparedPayloadBridge.payload_prepared c.loop cover (packed c v) mid done r hr k
end
end ExactFourierCircuits.UniformPreparedKernelTags

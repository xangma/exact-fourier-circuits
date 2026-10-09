import UniformPhysicalTensorPi
import UniformConditionalKernelNumeric
set_option autoImplicit false
namespace ExactFourierCircuits.UniformConditionalKernelPi
open UniformMachine UniformSectorPacking UniformSectorTensor
open UniformConditionalKernelLayout (Context Ready packed movementCost programFor)
noncomputable section
/-- The complete operational kernel acts simultaneously on every printed
axis under the actual physical mixed-radix order. RootBody remains open. -/
theorem execution {W F reserve n ordinal:ℕ} (child:Program) (c:Context W F reserve)
 (cost:ℕ → ℕ) (v:ℕ → Fin c.packing.volume → Scalar) (x:Fin n → ℂ) (s:State)
 (ready:Ready c ordinal v s) (hi:ordinal < (UniformProducedSectorChildABI.states c.physical).length)
 (root:UniformConditionalSectorLoop.RootBody child W n c.inverse.layout.B F reserve cost x)
 (positive:0 < W) (code:child.length+614 ≤ c.metadata.B) (pc:s.pc=0) (wb:WordBound c.metadata.B s):
 ∃u ticks,BoundedExecution (programFor child W) n x c.metadata.B s ticks u ∧
 ticks ≤ movementCost c+UniformConditionalSectorLoop.budget cost (UniformProducedSectorChildABI.states c.physical)+
  213*c.inverse.layout.total+W*(16*c.inverse.layout.total+12)+
  (12*W+20)*(UniformProducedSectorChildABI.states c.physical).length+57 ∧u.pc=child.length+613 ∧
 (∀r,r < W → ∀p:(i:Fin (UniformSectorPackingMachine.physicalAxes c.physical).length)→
  Fin ((UniformSectorPackingMachine.physicalAxes c.physical).get i).widths.sum,
  (u.scalarHeap (c.inverse.destination+r*(UniformSectorPackingMachine.physicalVolume c.physical)+
   (UniformPhysicalTensorPi.coordinate (UniformSectorPackingMachine.physicalAxes c.physical) p).val)).map Scalar.value=
  some ((OAI.ExactFourier.PiTensor.matrix
   (fun i:Fin (UniformSectorPackingMachine.physicalAxes c.physical).length=>
    UniformMatchingKernelGeometry.localKernel ((UniformSectorPackingMachine.physicalAxes c.physical).get i))).mulVec
    (fun q=>(v r (finCongr c.physicalVolume (UniformPhysicalTensorPi.coordinate
      (UniformSectorPackingMachine.physicalAxes c.physical) q))).value) p)) ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders :=by
 obtain ⟨u,ticks,run,cheap,up,stored,out,roots⟩:=
  UniformConditionalKernelNumeric.execution child c cost v x s ready hi root positive code pc wb
 refine ⟨u,ticks,run,cheap,up,?_,out,roots⟩
 intro r hr p
 have h:=stored r hr (UniformPhysicalTensorPi.coordinate (UniformSectorPackingMachine.physicalAxes c.physical) p)
 rw[UniformPhysicalTensorPi.original_action] at h
 exact h
end
end ExactFourierCircuits.UniformConditionalKernelPi

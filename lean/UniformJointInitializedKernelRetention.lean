import UniformJointInitializedKernelExecution
import UniformInitializedKernelRetention
set_option autoImplicit false
namespace ExactFourierCircuits.UniformJointInitializedKernelRetention
open UniformMachine UniformJointAllocation UniformJointConditionalKernelContext
open UniformConditionalKernelLayout (movementCost)
noncomputable section
/-- Real shared-slab layout supplies every cache separation inequality;
no extra readiness or desired cache preservation is an entry assumption. -/
theorem execution (c:Constants) {n:ℕ} (hn:0 < n) (roles:0 < c.roles) (child:Program)
 (physical:List UniformSectorPackingMachine.PhysicalAxis) (shape:PhysicalGeometry c n physical)
 (cost:ℕ→ℕ) (v:ℕ→Fin (UniformInitialPreparation.len n)→Scalar) (x:Fin n→ℂ) (s:State)
 (saved:UniformGlobalNatPreparation.SavedHeaders (UniformWorkingLength.nextPrime n) n
  (UniformInitialPreparation.ell n) (UniformInitialPreparation.len n) (UniformMasterRootMachine.order n) s)
 (allocated:UniformJointAllocationMachine.observed s=allocate c n)
 (banks:UniformGlobalRolePackingMachine.Banks (actualReserveContext c n hn roles physical shape).packing physical s)
 (source:UniformGlobalRolePackingMachine.Source (actualReserveContext c n hn roles physical shape).packing v s)
 (constants:UniformBinaryCStageMachine.Constants s)
 (root:UniformConditionalSectorLoop.RootBody child c.roles n (envelope c n) (allocate c n).fresh (payload c+5) cost x)
 (code:child.length+647 ≤ envelope c n) (pc:s.pc=0) (wb:WordBound (envelope c n) s):
 let g:=actualReserveContext c n hn roles physical shape
 ∃u ticks,BoundedExecution (UniformInitializedKernelExecution.programFor child c.roles) n x g.metadata.B s ticks u ∧
 ticks ≤ movementCost g+UniformConditionalSectorLoop.budget cost (UniformProducedSectorChildABI.states g.physical)+
  213*g.inverse.layout.total+c.roles*(16*g.inverse.layout.total+12)+
  (12*c.roles+20)*(UniformProducedSectorChildABI.states g.physical).length+90 ∧u.pc=child.length+646 ∧
 (∀r,r < c.roles → ∀j:Fin (UniformSectorPackingMachine.physicalVolume g.physical),
  (u.scalarHeap (g.inverse.destination+r*UniformSectorPackingMachine.physicalVolume g.physical+j.val)).map Scalar.value=
  some ((UniformSectorTensor.originalTensor (UniformSectorPackingMachine.physicalAxes g.physical)).mulVec
   (fun k=>(v r (finCongr g.physicalVolume k)).value) j)) ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,q < 2*slab c n → u.natHeap q=s.natHeap q) ∧
 (∀q,q < slab c n → u.scalarHeap q=s.scalarHeap q):=by
 obtain ⟨u,ticks,run,cheap,up,values,outputs,roots,nat,scalar⟩:=
  UniformInitializedKernelRetention.execution child (actualReserveContext c n hn roles physical shape)
   cost v x s (UniformJointKernelHeaderInstallation.input c hn roles physical shape s saved allocated)
   banks source constants root roles code pc wb
 refine ⟨u,ticks,run,cheap,up,values,outputs,roots,?_,?_⟩
 · intro q h
   apply nat q
   · change q < 7*slab c n;omega
   · change q < 6*slab c n;omega
   · change q < 12*slab c n;omega
   · change q < 8*slab c n;omega
   · change q < 11*slab c n;omega
 · intro q h
   apply scalar q
   · change q < 5*slab c n;omega
   · change q < 6*slab c n;omega
   · change q < 12*slab c n;omega
   · change q < 7*slab c n;omega
   · change q < 8*slab c n;omega
   · change q < 2*slab c n;omega

end
end ExactFourierCircuits.UniformJointInitializedKernelRetention

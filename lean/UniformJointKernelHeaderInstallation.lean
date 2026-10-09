import UniformKernelHeaderInstallation
import UniformJointConditionalKernelContext
import UniformJointAllocationMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformJointKernelHeaderInstallation
open UniformMachine UniformTensorMonomialMachine
open UniformJointAllocation UniformJointConditionalKernelContext
noncomputable section

/-- Every source of the actual32 block comes directly from the actual62
allocator's observed ABI and the real saved startup102/103 headers. -/
lemma input (c:Constants) {n:ℕ} (hn:0 < n) (roles:0 < c.roles)
 (physical:List UniformSectorPackingMachine.PhysicalAxis) (shape:PhysicalGeometry c n physical)
 (s:State) (saved:UniformGlobalNatPreparation.SavedHeaders (UniformWorkingLength.nextPrime n) n
  (UniformInitialPreparation.ell n) (UniformInitialPreparation.len n) (UniformMasterRootMachine.order n) s)
 (allocated:UniformJointAllocationMachine.observed s=allocate c n):
 UniformKernelHeaderInstallation.Input (actualReserveContext c n hn roles physical shape) s:=by
 constructor
 · exact saved.workingLength
 · exact congrArg (fun q=>q+1) saved.count
 · exact congrArg Addresses.tensorSource allocated
 · exact congrArg Addresses.packed allocated
 · exact congrArg Addresses.physicalRows allocated
 · exact congrArg Addresses.sectorSuffix allocated
 · exact congrArg Addresses.sectorStack allocated
 · exact congrArg Addresses.inverse allocated
 · exact congrArg Addresses.sectorRows allocated
 · exact congrArg Addresses.sectorSuffix allocated
 · exact congrArg Addresses.sectorStack allocated
 · exact congrArg Addresses.sectorDirectory allocated
 · exact congrArg Addresses.batchDirectory allocated
 · exact congrArg Addresses.child allocated
 · exact congrArg Addresses.fresh allocated
 · exact congrArg Addresses.sectorSuffix allocated
 · exact congrArg Addresses.sectorStack allocated
 · exact congrArg Addresses.inverse allocated
 · exact congrArg Addresses.sectorStack allocated
 · exact congrArg Addresses.tensorSource allocated

/-- Concrete shared geometry plus genuine already-produced data/tables,
without a supplied Ready record or any supplied recursive child action. -/
theorem execution (c:Constants) {n start:ℕ} (hn:0 < n) (roles:0 < c.roles)
 (physical:List UniformSectorPackingMachine.PhysicalAxis) (shape:PhysicalGeometry c n physical)
 (program:Program) (x:Fin n→ℂ) (v:ℕ→Fin (UniformInitialPreparation.len n)→Scalar) (s:State)
 (saved:UniformGlobalNatPreparation.SavedHeaders (UniformWorkingLength.nextPrime n) n
  (UniformInitialPreparation.ell n) (UniformInitialPreparation.len n) (UniformMasterRootMachine.order n) s)
 (allocated:UniformJointAllocationMachine.observed s=allocate c n)
 (banks:UniformGlobalRolePackingMachine.Banks (actualReserveContext c n hn roles physical shape).packing physical s)
 (source:UniformGlobalRolePackingMachine.Source (actualReserveContext c n hn roles physical shape).packing v s)
 (constants:UniformBinaryCStageMachine.Constants s)
 (code:BlockAt UniformKernelHeaderInstallation.block program start) (pc:s.pc=start)
 (room:start+32 ≤ envelope c n) (wb:WordBound (envelope c n) s):
 BoundedRuns program n x (envelope c n) s 32 (applyBlock UniformKernelHeaderInstallation.block s) ∧
 UniformConditionalKernelLayout.Ready (actualReserveContext c n hn roles physical shape) 0 v
  (applyBlock UniformKernelHeaderInstallation.block s) ∧
 (applyBlock UniformKernelHeaderInstallation.block s).natHeap=s.natHeap ∧
 (applyBlock UniformKernelHeaderInstallation.block s).scalarHeap=s.scalarHeap ∧
 (applyBlock UniformKernelHeaderInstallation.block s).scalarReg=s.scalarReg ∧
 (applyBlock UniformKernelHeaderInstallation.block s).outputs=s.outputs ∧
 (applyBlock UniformKernelHeaderInstallation.block s).rootOrders=s.rootOrders ∧
 (∀q,¬UniformKernelHeaderInstallation.Changed q→
  (applyBlock UniformKernelHeaderInstallation.block s).natReg q=s.natReg q):=
 UniformKernelHeaderInstallation.execution (actualReserveContext c n hn roles physical shape)
  program x v s (input c hn roles physical shape s saved allocated) banks source constants code pc room wb
end
end ExactFourierCircuits.UniformJointKernelHeaderInstallation

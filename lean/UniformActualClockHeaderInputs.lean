import UniformActualClockEntry
import UniformProducedAllAxisGeometry
set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualClockHeaderInputs
open UniformMachine UniformJointAllocation
open UniformActualGlobalConstants (constants)
open UniformActualGlobalTickContext
noncomputable section

/-- The real allocator observation and saved size/count cells discharge all
ordinary actual32 kernel input links, for every newly printed axis family. -/
lemma kernel_input {n:ℕ} (hn:0<n) (a:Geometry n) (s:State)
 (volume:s.natReg 103=UniformInitialPreparation.len n)
 (count:s.natReg 102+1=UniformAllAxisSeedPreparation.axisCount n)
 (allocated:UniformJointAllocationMachine.observed s=allocate constants n):
 UniformKernelHeaderInstallation.Input (kernel hn a) s:=by
 constructor
 · exact volume
 · exact count
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

/-- The same observed fields discharge the actual17 diagonal header block;
the coefficient bank is the genuine fresh bank following allW input arrays. -/
lemma diagonal_input {n:ℕ} (hn:0<n) (a:Geometry n) (s:State)
 (volume:s.natReg 103=UniformInitialPreparation.len n)
 (count:s.natReg 102+1=UniformAllAxisSeedPreparation.axisCount n)
 (allocated:UniformJointAllocationMachine.observed s=allocate constants n):
 UniformDiagonalHeaderInstallation.Input (UniformActualGlobalTickContext.diagonal hn a).rows (UniformActualGlobalTickContext.diagonal hn a).tensor s:=by
 constructor
 · exact count
 · exact count
 · exact congrArg Addresses.factorDirectory allocated
 · exact congrArg Addresses.tensorRows allocated
 · exact congrArg Addresses.permutation allocated
 · have source:=congrArg Addresses.tensorSource allocated
   change s.natReg 6026=(allocate constants n).tensorSource at source
   change s.natReg 6026+UniformRecursiveSelfCallMachine.W*s.natReg 103=
    UniformJointDiagonalHeaderInstallation.coefficient constants n
   rw[source,volume]
   rfl
 · exact volume
 · exact congrArg Addresses.tensorSource allocated
 · exact congrArg Addresses.native allocated
 · exact congrArg Addresses.tensorRows allocated
 · exact congrArg Addresses.tensorNatStack allocated
 · exact congrArg Addresses.tensorScalarStack allocated
lemma source {n:ℕ} (hn:0<n) (a:Geometry n)
 (v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar) (s:State)
 (ready:UniformActualClockEntry.Source n v s):
 UniformGlobalRolePackingMachine.Source (kernel hn a).packing v s:=ready
end
end ExactFourierCircuits.UniformActualClockHeaderInputs

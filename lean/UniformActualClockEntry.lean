import UniformActualGlobalClockProgram
import UniformActualGlobalConstants
import UniformFourierAxisWorkspace
import UniformPhysicalSynchronizedSchedule
import UniformJointAllocationMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualClockEntry
open UniformMachine
open UniformActualGlobalConstants (constants)
noncomputable section

def sourceBase (n:ℕ):ℕ:=2*UniformJointAllocation.slab constants n
abbrev volume (n:ℕ):ℕ:=UniformInitialPreparation.len n
abbrev roles:ℕ:=UniformRecursiveSelfCallMachine.W

def Source (n:ℕ) (v:ℕ→Fin (volume n)→Scalar) (s:State):Prop:=
 ∀r,r<roles→∀j:Fin (volume n),s.scalarHeap (sourceBase n+r*volume n+j.val)=some (v r j)
def Prepared {n:ℕ} (v:ℕ→Fin (volume n)→Scalar):Prop:=
 ∀r,r<roles→∀j:Fin (volume n),(v r j).dependent=false

/-- Exact ordinary clock entry ABI after the charged role loader. The genuine
retained cache contents are a separate producer theorem, rather than a guessed
ready condition hidden in these scalar input or address fields. -/
structure Input (n H seedDirectory:ℕ) (v:ℕ→Fin (volume n)→Scalar) (s:State):Prop where
 pc:s.pc=0
 bound:WordBound (UniformJointAllocation.envelope constants n) s
 code:UniformActualGlobalClockProgram.program.length≤UniformJointAllocation.envelope constants n
 allocator:UniformJointAllocationMachine.observed s=UniformJointAllocation.allocate constants n
 axisCount:s.natReg 102+1=UniformAllAxisSeedPreparation.axisCount n
 volume:s.natReg 103=UniformActualClockEntry.volume n
 horizon:s.natReg 5921=H
 natFrontier:s.natReg 6819=UniformGlobalCalendarArena.natBase constants n
 scalarFrontier:s.natReg 6821=UniformGlobalCalendarArena.scalarBase constants n
 seed:s.natReg 6904=seedDirectory
 initialNat:s.natReg 6909=UniformJointCacheAllocation.natStart constants n
 initialScalar:s.natReg 6910=UniformJointCacheAllocation.scalarStart constants n
 source:Source n v s
 constants:UniformBinaryCStageMachine.Constants s
 length:∀i,(UniformSynchronizedLayers.localSchedules n i).length≤H

/-- Exact numerical endpoint expected by the outer three-transform proof. -/
def Numeric (n:ℕ) (v:ℕ→Fin (volume n)→Scalar) (u:State):Prop:=
 ∀r,r<roles→∀j:Fin (volume n),
 (u.scalarHeap (sourceBase n+r*volume n+j.val)).map Scalar.value=
  some ((UniformPhysicalSynchronizedSchedule.fourier n).mulVec (fun k=>(v r k).value) j)

def PreparedOutput (n:ℕ) (u:State):Prop:=
 ∀r,r<roles→∀j:Fin (volume n),
 (u.scalarHeap (sourceBase n+r*volume n+j.val)).map Scalar.dependent=some false
end
end ExactFourierCircuits.UniformActualClockEntry

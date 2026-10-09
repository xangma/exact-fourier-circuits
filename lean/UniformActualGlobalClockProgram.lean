import UniformFourierAxisPrepareMachine
import UniformActualGlobalConstants
import UniformGlobalClockPlacement

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualGlobalClockProgram
open UniformMachine UniformAssembly UniformActualGlobalConstants
noncomputable section
attribute [local irreducible] Nat.add UniformRecursiveSavingProgram.program

/-- One fixed clock/all-axis program, including the actual389 preparation,
actual281 fold, actual69 partitioner and proved same recursive kernel. -/
def program:Program:=UniformGlobalClockConductor.programFor UniformFourierAxisPrepareMachine.program
 UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W
lemma program_length:program.length=UniformRecursiveSavingProgram.program.length+1572:=by
 rw[program,UniformGlobalClockConductor.program_length,UniformFourierAxisPrepareMachine.program_length]
 omega

lemma generic_code_bound (c:UniformJointAllocation.Constants) (p:ℕ) (size:p ≤ c.code):
 p+1572 ≤ UniformJointAllocation.fixed c:=by
 rw[UniformJointAllocation.fixed]
 omega
lemma fixed_code_bound:program.length ≤ UniformJointAllocation.fixed constants:=by
 rw[program_length]
 exact generic_code_bound constants _ code_le
lemma code_bound (n:ℕ):program.length ≤ UniformJointAllocation.envelope constants n:=
 fixed_code_bound.trans (envelope_bound _ _)

lemma prepare_code:CodeAt UniformFourierAxisPrepareMachine.program program 11 400:=by
 have h:=UniformGlobalClockConductor.prepare_code UniformFourierAxisPrepareMachine.program
  UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W
 simpa only[program,Nat.reduceAdd,UniformGlobalClockConductor.dispatchBase,UniformFourierAxisPrepareMachine.program_length] using h
lemma dispatch_code:CodeAt UniformGlobalCalendarDispatch.program program 400 681:=by
 have h:=UniformGlobalClockConductor.dispatch_code UniformFourierAxisPrepareMachine.program
  UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W
 simpa only[program,Nat.reduceAdd,UniformGlobalClockConductor.dispatchBase,UniformGlobalClockConductor.adapterBase,
  UniformFourierAxisPrepareMachine.program_length] using h
lemma adapter_code:CodeAt UniformGlobalAxisUnionAdapter.program program 681 750:=by
 have h:=UniformGlobalClockConductor.adapter_code UniformFourierAxisPrepareMachine.program
  UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W
 simpa only[program,Nat.reduceAdd,UniformGlobalClockConductor.dispatchBase,UniformGlobalClockConductor.adapterBase,
  UniformGlobalClockConductor.advanceBase,UniformFourierAxisPrepareMachine.program_length] using h
lemma kernel_code:CodeAt
 (UniformGlobalKernelDiagonalAssembly.programFor UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W)
 program 756 (UniformRecursiveSavingProgram.program.length+1569):=by
 have h:=UniformGlobalClockConductor.kernel_code UniformFourierAxisPrepareMachine.program
  UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W
 have site:UniformGlobalClockConductor.kernelBase UniformFourierAxisPrepareMachine.program=756:=by
  simp only[UniformGlobalClockConductor.kernelBase,UniformGlobalClockConductor.dispatchBase,
   UniformGlobalClockConductor.adapterBase,UniformGlobalClockConductor.advanceBase,
   UniformFourierAxisPrepareMachine.program_length]
 have finish:UniformGlobalClockConductor.tickBase UniformFourierAxisPrepareMachine.program
  UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W=
  UniformRecursiveSavingProgram.program.length+1569:=by
  rw[UniformGlobalClockConductor.tickBase,site,UniformGlobalKernelDiagonalAssembly.program_length]
  omega
 simpa only[program,site,finish] using h
end
end ExactFourierCircuits.UniformActualGlobalClockProgram

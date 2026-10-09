import UniformFinalOuterProgram
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalStartupCode
open UniformMachine UniformAssembly UniformSequentialAssembly UniformFinalOuterProgram
attribute [local irreducible] UniformAllAxisConjugatePreparation.fullProgram
 UniformJointAllocationMachine.program UniformJointCacheWorkspaceMachine.program UniformAxisCacheWholeProgram.program
lemma initial_code(table:Program):CodeAt UniformAllAxisConjugatePreparation.fullProgram (programFor table) 0 1460:=by
 have h:=stage_code [] UniformAllAxisConjugatePreparation.fullProgram ((stagesFor table).drop 1)
 have shape:([]++UniformAllAxisConjugatePreparation.fullProgram::(stagesFor table).drop 1)=stagesFor table:=rfl
 rw[shape] at h
 simpa only[programFor,Nat.reduceAdd,size,Nat.zero_add,UniformAllAxisConjugatePreparation.fullProgram_length] using h
lemma allocation_code(table:Program):CodeAt (UniformJointAllocationMachine.program UniformActualGlobalConstants.constants) (programFor table) 1460 1522:=by
 let before:List Program:=[UniformAllAxisConjugatePreparation.fullProgram]
 have h:=stage_code before (UniformJointAllocationMachine.program UniformActualGlobalConstants.constants) ((stagesFor table).drop 2)
 have shape:before++UniformJointAllocationMachine.program UniformActualGlobalConstants.constants::(stagesFor table).drop 2=stagesFor table:=rfl
 rw[shape] at h
 simpa only[programFor,Nat.reduceAdd,before,size,Nat.add_zero,UniformAllAxisConjugatePreparation.fullProgram_length,
  UniformJointAllocationMachine.program_length] using h
lemma workspace_code(table:Program):CodeAt UniformJointCacheWorkspaceMachine.program (programFor table) 1522 1589:=by
 let before:List Program:=[UniformAllAxisConjugatePreparation.fullProgram,
  UniformJointAllocationMachine.program UniformActualGlobalConstants.constants]
 have h:=stage_code before UniformJointCacheWorkspaceMachine.program ((stagesFor table).drop 3)
 have shape:before++UniformJointCacheWorkspaceMachine.program::(stagesFor table).drop 3=stagesFor table:=rfl
 rw[shape] at h
 simpa only[programFor,Nat.reduceAdd,before,size,Nat.add_zero,UniformAllAxisConjugatePreparation.fullProgram_length,
  UniformJointAllocationMachine.program_length,UniformJointCacheWorkspaceMachine.program_length] using h
lemma cache_code(table:Program):CodeAt UniformAxisCacheWholeProgram.program (programFor table) 1589 6243:=by
 let before:List Program:=[UniformAllAxisConjugatePreparation.fullProgram,
  UniformJointAllocationMachine.program UniformActualGlobalConstants.constants,UniformJointCacheWorkspaceMachine.program]
 have h:=stage_code before UniformAxisCacheWholeProgram.program ((stagesFor table).drop 4)
 have shape:before++UniformAxisCacheWholeProgram.program::(stagesFor table).drop 4=stagesFor table:=rfl
 rw[shape] at h
 simpa only[programFor,Nat.reduceAdd,before,size,Nat.add_zero,UniformAllAxisConjugatePreparation.fullProgram_length,
  UniformJointAllocationMachine.program_length,UniformJointCacheWorkspaceMachine.program_length,
  UniformAxisCacheWholeProgram.program_length] using h
end ExactFourierCircuits.UniformFinalStartupCode

import UniformSequentialAssembly
import UniformPhysicalCRTTableHeaderProgram
import UniformFinalOuterHeaders
import UniformFastPhysicalCRTMachine
import UniformPhysicalCRTConsumerMachine
import UniformInitialCoreRetention
import UniformJointAllocationMachine
import UniformJointCacheWorkspaceMachine
import UniformAxisCacheWholeExecution
import UniformActualGlobalClockProgram
import UniformRoleInputMachine
import UniformKernelSpectrumCopy
import UniformRolePointwiseMachine
import UniformChirpOutputMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalOuterProgram
open UniformMachine UniformAssembly UniformSequentialAssembly
noncomputable section
attribute [local irreducible] Nat.add Nat.mul UniformRecursiveSavingProgram.program UniformActualGlobalClockProgram.program

/-- One literal program, independent of n and x. The prepared kernel transform
is saved before input data are loaded; the three complete clock traversals use
identical fixed code. Every helper halt becomes a charged continuation jump. -/
def stagesFor(table:Program):List Program:=[
 UniformAllAxisConjugatePreparation.fullProgram,
 UniformJointAllocationMachine.program UniformActualGlobalConstants.constants,
 UniformJointCacheWorkspaceMachine.program,
 UniformAxisCacheWholeProgram.program,
 natProgram UniformPhysicalCRTTableHeaders.operations,
 table,
 natProgram (UniformFinalOuterHeaders.roleArgs UniformRecursiveSelfCallMachine.W true),
 UniformRoleInputMachine.program,
 UniformActualGlobalClockProgram.program,
 UniformKernelSpectrumCopy.program,
 natProgram (UniformFinalOuterHeaders.roleArgs UniformRecursiveSelfCallMachine.W false),
 UniformRoleInputMachine.program,
 UniformPhysicalCRTConsumerMachine.alphaProgram,
 UniformActualGlobalClockProgram.program,
 UniformRolePointwiseMachine.program,
 UniformPhysicalCRTConsumerMachine.program,
 UniformActualGlobalClockProgram.program,
 UniformPhysicalCRTConsumerMachine.program,
 natProgram UniformFinalOuterHeaders.output,
 UniformChirpOutputMachine.program]

/-- The amortized mixed-radix table producer is fixed once for all lengths. -/
def stages:List Program:=stagesFor UniformFastPhysicalCRTMachine.program
def programFor(table:Program):Program:=UniformSequentialAssembly.program (stagesFor table)
def program:Program:=programFor UniformFastPhysicalCRTMachine.program
lemma stages_length(table:Program):(stagesFor table).length=20:=rfl
lemma stages_size(table:Program):size (stagesFor table)=
 3*UniformRecursiveSavingProgram.program.length+table.length+11248:=by
 simp only[stagesFor,size,UniformAllAxisConjugatePreparation.fullProgram_length,
  UniformJointAllocationMachine.program_length,UniformJointCacheWorkspaceMachine.program_length,
  UniformAxisCacheWholeProgram.program_length,natProgram_length,
  UniformPhysicalCRTTableHeaders.operations_length,
  UniformFinalOuterHeaders.roleArgs_length,Bool.false_eq_true,ite_false,ite_true,
  UniformRoleInputMachine.program_length,UniformActualGlobalClockProgram.program_length,
  UniformKernelSpectrumCopy.program_length,UniformPhysicalCRTConsumerMachine.alphaProgram_length,
  UniformRolePointwiseMachine.program_length,UniformPhysicalCRTConsumerMachine.program_length,
  UniformFinalOuterHeaders.output_length,UniformChirpOutputMachine.program_length]
 omega
lemma programFor_length(table:Program):(programFor table).length=
 3*UniformRecursiveSavingProgram.program.length+table.length+11249:=by
 rw[programFor,UniformSequentialAssembly.program_length,stages_size]
lemma program_length:program.length=3*UniformRecursiveSavingProgram.program.length+
 UniformFastPhysicalCRTMachine.program.length+11249:=programFor_length _
lemma halt_at(table:Program):(programFor table)[size (stagesFor table)]?=some .halt:=
 UniformSequentialAssembly.halt_at (stagesFor table)

/-- The actual finite code fits the same conservative shared slab. Neither
its enormous recursive printer nor its role enumeration is evaluated. -/
lemma code_slab(table:Program)(n:ℕ)(tableFit:table.length≤
 UniformJointAllocation.fixed UniformActualGlobalConstants.constants):
 (programFor table).length≤UniformJointAllocation.slab UniformActualGlobalConstants.constants n:=by
 have p:UniformRecursiveSavingProgram.program.length≤UniformJointAllocation.fixed UniformActualGlobalConstants.constants:=
  UniformActualGlobalConstants.code_le.trans (UniformJointAllocation.program_le _)
 have large:=UniformJointAllocation.fixed_large UniformActualGlobalConstants.constants
 have pow:1≤(n+2)^19:=Nat.one_le_pow _ _ (by omega)
 have scale:100000*(UniformJointAllocation.fixed UniformActualGlobalConstants.constants+1)≤
  UniformJointAllocation.slab UniformActualGlobalConstants.constants n:=
  Nat.le_mul_of_pos_right _ pow
 rw[programFor_length]
 omega
lemma code_envelope(table:Program)(n:ℕ)(tableFit:table.length≤
 UniformJointAllocation.fixed UniformActualGlobalConstants.constants):
 (programFor table).length≤UniformJointAllocation.envelope UniformActualGlobalConstants.constants n:=
 (code_slab table n tableFit).trans (by unfold UniformJointAllocation.envelope;omega)

end
end ExactFourierCircuits.UniformFinalOuterProgram

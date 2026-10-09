import UniformFinalOuterProgram
import UniformSequentialExecution

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.3 three-transform construction and §5.4 Theorem 1.1 proof,
PDF pp.22-24 (`eq:chirp`, `thm:main`), with the model in §1.1, PDF p.2 (`sec:model`).

Startup, header, continuation and output bookkeeping refines the fixed
deterministic program. There is no separate paper counterpart for these state
layouts; the surrounding paper argument requires their preparation/index cost.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalOuterSuffix
open UniformMachine UniformAssembly UniformSequentialAssembly UniformSequentialExecution
open UniformTensorMonomialMachine (setPC)
noncomputable section
local notation "p"=>UniformFinalOuterProgram.program
local notation "c"=>UniformActualGlobalConstants.constants
local notation "B" n=>UniformJointAllocation.envelope c n
attribute [local irreducible] UniformRecursiveSavingProgram.program UniformActualGlobalClockProgram.program
 UniformAllAxisConjugatePreparation.fullProgram UniformJointAllocationMachine.program
 UniformJointCacheWorkspaceMachine.program UniformAxisCacheWholeProgram.program

def prelude:List Program:=[UniformAllAxisConjugatePreparation.fullProgram,
 UniformJointAllocationMachine.program c,UniformJointCacheWorkspaceMachine.program,
 UniformAxisCacheWholeProgram.program,natProgram UniformPhysicalCRTTableHeaders.operations,
 UniformFastPhysicalCRTMachine.program]
def suffix:List Program:=(UniformFinalOuterProgram.stages).drop 6
lemma shape:prelude++suffix=UniformFinalOuterProgram.stages:=rfl
lemma prelude_size:size prelude=6316:=by
 simp only[prelude,size,UniformAllAxisConjugatePreparation.fullProgram_length,
  UniformJointAllocationMachine.program_length,UniformJointCacheWorkspaceMachine.program_length,
  UniformAxisCacheWholeProgram.program_length,natProgram_length,
  UniformPhysicalCRTTableHeaders.operations_length,UniformFastPhysicalCRTMachine.program_length]
lemma full_size:6316+size suffix=size UniformFinalOuterProgram.stages:=by
 rw[←prelude_size,←size_append,shape]
lemma contains:Contains p 6316 suffix:=by
 have h:=contains_suffix (q:=p) (base:=0) (before:=prelude) (ps:=suffix)
  (by rw[shape];exact program_contains _)
 simpa only[Nat.zero_add,prelude_size] using h
lemma code_fit(n:ℕ):(p).length≤B n:=by
 apply UniformFinalOuterProgram.code_envelope
 rw[UniformFastPhysicalCRTMachine.program_length]
 have:=UniformJointAllocation.fixed_large c
 omega

/-- Join the genuinely executed preparation prefix to the genuinely executed
remaining fourteen stages and the sole final halt. -/
/- Paper stage: Implementation sequential join for §5.4 deterministic algorithm, PDF pp.23-24: prefix and suffix share their endpoint; relocation charges the actual continuation and sole final halt. -/
theorem execution{n ti ts:ℕ}{x:Fin n→ℂ}{s u:State}
 (prefixRun:BoundedRuns p n x (B n) initial ti s)(pc:s.pc=6316)
 (tailRun:LocalStages n (B n) x suffix s ts u):
 BoundedExecution p n x (B n) initial (ti+ts+1)
  (UniformTensorMonomialMachine.setPC u (size UniformFinalOuterProgram.stages)):=by
 have fit:size UniformFinalOuterProgram.stages≤B n:=by
  have h:=code_fit n
  rw[UniformFinalOuterProgram.program,UniformFinalOuterProgram.programFor,
   UniformSequentialAssembly.program_length] at h
  change size (UniformFinalOuterProgram.stagesFor UniformFastPhysicalCRTMachine.program)≤B n
  omega
 have run:=tailRun.runs contains (by rw[full_size];exact fit)
 change BoundedRuns p n x (B n) (setPC s 6316) ts (setPC u (6316+size suffix)) at run
 have start:(setPC s 6316)=s:=by rw[←pc];rfl
 rw[start,full_size] at run
 have halted:(p)[size UniformFinalOuterProgram.stages]?=some .halt:=
  UniformFinalOuterProgram.halt_at UniformFastPhysicalCRTMachine.program
 have done:BoundedExecution p n x (B n)
  (setPC u (size UniformFinalOuterProgram.stages)) 1
  (setPC u (size UniformFinalOuterProgram.stages)):=.halt run.final_bound (by
   simp only[step,setPC,halted])
 simpa only[Nat.add_assoc] using (prefixRun.trans run).executes done

end
end ExactFourierCircuits.UniformFinalOuterSuffix

import UniformActualGlobalClockProgram
import UniformGlobalClockAdvanceExecution

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualAxisPreparedCycle
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (setPC)
noncomputable section
attribute [local irreducible] Nat.add UniformGlobalClockConductor.programFor UniformActualGlobalClockProgram.program UniformRecursiveSavingProgram.program

lemma placed_reset (s:State) (base:ℕ):placed base (setPC s 0)=setPC s base:=by
 simp only[placed,setPC,Nat.add_zero]

/-- Internal continuity for the real preparation entry. Both arguments are
actual runs of the fixed bytecode. This lemma makes no cache, numerical
output, handler, or program-correctness assumption. -/
theorem join_preparation {n B prepareTicks suffixTicks:ℕ} (x:Fin n→ℂ) (s v u:State)
 (pc:s.pc=10) (unfinished:s.natReg 5922 < s.natReg 5938) (wb:WordBound B s)
 (code:UniformActualGlobalClockProgram.program.length ≤ B)
 (prepare:BoundedExecution UniformFourierAxisPrepareMachine.program n x B (setPC s 0) prepareTicks v)
 (suffix:BoundedRuns UniformActualGlobalClockProgram.program n x B (setPC v 400) suffixTicks u):
 BoundedRuns UniformActualGlobalClockProgram.program n x B s (1+(prepareTicks+suffixTicks)) u:=by
 have code':(UniformGlobalClockConductor.programFor UniformFourierAxisPrepareMachine.program
  UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W).length ≤ B:=by
  simpa only[UniformActualGlobalClockProgram.program] using code
 have branch:=UniformGlobalClockAdvanceExecution.axis_branch UniformFourierAxisPrepareMachine.program
  UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W x s pc wb code'
 have branch':BoundedRuns UniformActualGlobalClockProgram.program n x B s 1 (setPC s 11):=by
  simpa only[UniformActualGlobalClockProgram.program,unfinished,ite_true] using branch
 have size:11+UniformFourierAxisPrepareMachine.program.length ≤ B:=by
  rw[UniformFourierAxisPrepareMachine.program_length]
  rw[UniformActualGlobalClockProgram.program_length] at code
  omega
 have extent:400 ≤ B:=by rw[UniformFourierAxisPrepareMachine.program_length] at size;omega
 have moved:=UniformBoundedAssembly.boundedExecution_placed UniformActualGlobalClockProgram.prepare_code size extent prepare
 rw[placed_reset] at moved
 exact branch'.trans (moved.trans suffix)

/-- A local actual tick proof is used at the literal fixed kernel entry;
resetting the proof-level PC preserves every real register and tagged cell. -/
lemma kernel_entry (s:State) (pc:s.pc=756):
 placed (UniformGlobalClockConductor.kernelBase UniformFourierAxisPrepareMachine.program) (setPC s 0)=s:=by
 have site:UniformGlobalClockConductor.kernelBase UniformFourierAxisPrepareMachine.program=756:=by
  simp only[UniformGlobalClockConductor.kernelBase,UniformGlobalClockConductor.advanceBase,
   UniformGlobalClockConductor.adapterBase,UniformGlobalClockConductor.dispatchBase,
   UniformFourierAxisPrepareMachine.program_length]
 rw[site,placed_reset,←pc]
 cases s;rfl
end
end ExactFourierCircuits.UniformActualAxisPreparedCycle

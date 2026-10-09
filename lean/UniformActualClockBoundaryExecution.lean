import UniformActualAxisPreparedCycle
set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualClockBoundaryExecution
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (setPC applyBlock applyBlock_pc)
open UniformGlobalClockConductor (boot axisBoot programFor)
noncomputable section
attribute [local irreducible] Nat.add programFor UniformActualGlobalClockProgram.program UniformRecursiveSavingProgram.program

lemma code_bound {B:ℕ} (code:UniformActualGlobalClockProgram.program.length≤B):
 (programFor UniformFourierAxisPrepareMachine.program UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W).length≤B:=by
 simpa only[UniformActualGlobalClockProgram.program] using code

/-- The real boot saves the physically measured cache ends and starts clock0. -/
theorem boot_execution {n B:ℕ} (x:Fin n→ℂ) (s:State) (pc:s.pc=0)
 (code:UniformActualGlobalClockProgram.program.length≤B) (count:s.natReg 102+1≤B) (wb:WordBound B s):
 BoundedRuns UniformActualGlobalClockProgram.program n x B s 5 (applyBlock boot s) ∧
 (applyBlock boot s).pc=5 ∧
 (applyBlock boot s).natReg 5920=0 ∧(applyBlock boot s).natReg 5921=s.natReg 5921 ∧
 (applyBlock boot s).natReg 5936=s.natReg 6819 ∧(applyBlock boot s).natReg 5937=s.natReg 6821 ∧
 (applyBlock boot s).natReg 5938=s.natReg 102+1 ∧(applyBlock boot s).natReg 5939=1:=by
 have space:=UniformGlobalClockAdvanceExecution.control_space UniformFourierAxisPrepareMachine.program
  UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W (code_bound code)
 have run:=UniformGlobalClockControl.boot_execution
  (programFor UniformFourierAxisPrepareMachine.program UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W)
  x s (UniformGlobalClockPlacement.boot_code _ _ _) pc (by omega) count wb
 refine ⟨?_,?_,UniformGlobalClockControl.boot_headers s⟩
 · simpa only[UniformActualGlobalClockProgram.program] using run
 · rw[applyBlock_pc,UniformGlobalClockConductor.boot_length,pc]

/-- A true clock branch resets the genuine fresh arena frontiers and axis
index by the four actual axisBoot instructions, reaching pc10 in five ticks. -/
theorem tick_start {n B:ℕ} (x:Fin n→ℂ) (s:State) (pc:s.pc=5)
 (unfinished:s.natReg 5920<s.natReg 5921) (one:s.natReg 5939=1)
 (code:UniformActualGlobalClockProgram.program.length≤B) (wb:WordBound B s):
 BoundedRuns UniformActualGlobalClockProgram.program n x B s 5 (applyBlock axisBoot (setPC s 6)) ∧
 (applyBlock axisBoot (setPC s 6)).pc=10 ∧
 (applyBlock axisBoot (setPC s 6)).natReg 5922=0 ∧
 (applyBlock axisBoot (setPC s 6)).natReg 5923=s.natReg 6020 ∧
 (applyBlock axisBoot (setPC s 6)).natReg 5924=s.natReg 5936 ∧
 (applyBlock axisBoot (setPC s 6)).natReg 5925=s.natReg 5937:=by
 have space:=UniformGlobalClockAdvanceExecution.control_space UniformFourierAxisPrepareMachine.program
  UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W (code_bound code)
 have branch:=UniformGlobalClockAdvanceExecution.clock_branch UniformFourierAxisPrepareMachine.program
  UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W x s pc wb (code_bound code)
 have branch':BoundedRuns UniformActualGlobalClockProgram.program n x B s 1 (setPC s 6):=by
  simpa only[UniformActualGlobalClockProgram.program,unfinished,ite_true] using branch
 have axis:=UniformGlobalClockControl.axis_execution
  (programFor UniformFourierAxisPrepareMachine.program UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W)
  x (setPC s 6) (UniformGlobalClockPlacement.axis_code _ _ _) rfl (by omega) one branch'.final_bound
 have axis':BoundedRuns UniformActualGlobalClockProgram.program n x B (setPC s 6) 4
  (applyBlock axisBoot (setPC s 6)):=by
  simpa only[UniformActualGlobalClockProgram.program] using axis
 refine ⟨branch'.trans axis',?_,UniformGlobalClockControl.axis_headers (setPC s 6) one⟩
 rw[applyBlock_pc,UniformGlobalClockConductor.axisBoot_length]
 rfl

/-- Once every actual axis was printed, the literal branch enters the fixed
proved common-C/diagonal consumer at pc756. -/
theorem kernel_branch {n B:ℕ} (x:Fin n→ℂ) (s:State) (pc:s.pc=10)
 (finished:s.natReg 5938 ≤ s.natReg 5922)
 (code:UniformActualGlobalClockProgram.program.length≤B) (wb:WordBound B s):
 BoundedRuns UniformActualGlobalClockProgram.program n x B s 1 (setPC s 756):=by
 have branch:=UniformGlobalClockAdvanceExecution.axis_branch UniformFourierAxisPrepareMachine.program
  UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W x s pc wb (code_bound code)
 have site:UniformGlobalClockConductor.kernelBase UniformFourierAxisPrepareMachine.program=756:=by
  simp only[UniformGlobalClockConductor.kernelBase,UniformGlobalClockConductor.advanceBase,
   UniformGlobalClockConductor.adapterBase,UniformGlobalClockConductor.dispatchBase,
   UniformFourierAxisPrepareMachine.program_length]
 simpa only[UniformActualGlobalClockProgram.program,show ¬s.natReg 5922<s.natReg 5938 by omega,ite_false,site] using branch

/-- The final false clock branch and literal halt are both charged. -/
theorem halt_execution {n B:ℕ} (x:Fin n→ℂ) (s:State) (pc:s.pc=5)
 (finished:s.natReg 5921 ≤ s.natReg 5920)
 (code:UniformActualGlobalClockProgram.program.length≤B) (wb:WordBound B s):
 BoundedExecution UniformActualGlobalClockProgram.program n x B s 2
  (setPC s (UniformGlobalClockConductor.finalPC UniformFourierAxisPrepareMachine.program
   UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W)):=by
 let target:=UniformGlobalClockConductor.finalPC UniformFourierAxisPrepareMachine.program
  UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W
 have branch:=UniformGlobalClockAdvanceExecution.clock_branch UniformFourierAxisPrepareMachine.program
  UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W x s pc wb (code_bound code)
 have branch':BoundedRuns UniformActualGlobalClockProgram.program n x B s 1 (setPC s target):=by
  simpa only[UniformActualGlobalClockProgram.program,show ¬s.natReg 5920<s.natReg 5921 by omega,ite_false,target] using branch
 have stop:=UniformGlobalClockAdvanceExecution.halt_execution UniformFourierAxisPrepareMachine.program
  UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W x (setPC s target) rfl branch'.final_bound
 have stop':BoundedExecution UniformActualGlobalClockProgram.program n x B (setPC s target) 1 (setPC s target):=by
  simpa only[UniformActualGlobalClockProgram.program] using stop
 exact branch'.executes stop'
end
end ExactFourierCircuits.UniformActualClockBoundaryExecution

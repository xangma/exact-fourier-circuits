import UniformGlobalClockControl
import UniformGlobalClockPlacement

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalClockAdvanceExecution
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (setPC Op applyBlock applyBlock_pc)
open UniformGlobalClockConductor
noncomputable section
attribute [local irreducible] Nat.add programFor

lemma control_space {B:ℕ} (prepare child:Program) (W:ℕ)
 (code:(programFor prepare child W).length ≤ B):
 advanceBase prepare+6 ≤ B ∧tickBase prepare child W+2 ≤ B ∧
 kernelBase prepare ≤ B ∧finalPC prepare child W ≤ B ∧11 ≤ B:=by
 rw[program_length] at code
 simp only[advanceBase,adapterBase,dispatchBase,tickBase,kernelBase,finalPC,
  UniformGlobalKernelDiagonalAssembly.program_length]
 omega

theorem axis_execution {n B:ℕ} (prepare child:Program) (W:ℕ) (x:Fin n→ℂ) (s:State)
 (pc:s.pc=advanceBase prepare) (one:s.natReg 5939=1) (wb:WordBound B s)
 (code:(programFor prepare child W).length ≤ B)
 (index:s.natReg 5922+1 ≤ B) (directory:s.natReg 5923+2 ≤ B):
 BoundedRuns (programFor prepare child W) n x B s 6 (setPC (applyBlock advance s) 10) ∧
 (setPC (applyBlock advance s) 10).natReg 5922=s.natReg 5922+1 ∧
 (setPC (applyBlock advance s) 10).natReg 5923=s.natReg 5923+2 ∧
 (setPC (applyBlock advance s) 10).natReg 5924=s.natReg 5934 ∧
 (setPC (applyBlock advance s) 10).natReg 5925=s.natReg 5935:=by
 have space:=control_space prepare child W code
 have advanceRun:=UniformGlobalClockControl.advance_execution (programFor prepare child W) x s
  (UniformGlobalClockPlacement.advance_code prepare child W) pc (by omega) one wb index directory
 have after:(applyBlock advance s).pc=advanceBase prepare+5:=by
  rw[applyBlock_pc,advance_length,pc]
 have jump:=UniformMatchingAxisTableMachine.jump_runs (programFor prepare child W) B n 10 x
  (applyBlock advance s) (by rw[after];exact UniformGlobalClockPlacement.axis_backedge prepare child W)
  advanceRun.final_bound (by omega)
 exact ⟨advanceRun.trans jump,UniformGlobalClockControl.advance_headers s one⟩

theorem tick_execution {n B:ℕ} (prepare child:Program) (W:ℕ) (x:Fin n→ℂ) (s:State)
 (pc:s.pc=tickBase prepare child W) (one:s.natReg 5939=1) (wb:WordBound B s)
 (code:(programFor prepare child W).length ≤ B) (unfinished:s.natReg 5920 < s.natReg 5921):
 BoundedRuns (programFor prepare child W) n x B s 2 (setPC (applyBlock tickAdvance s) 5) ∧
 (setPC (applyBlock tickAdvance s) 5).natReg 5920=s.natReg 5920+1:=by
 have space:=control_space prepare child W code
 have tick:=UniformGlobalClockControl.tick_execution (programFor prepare child W) x s
  (UniformGlobalClockPlacement.tick_code prepare child W) pc (by omega) one wb unfinished
 have after:(applyBlock tickAdvance s).pc=tickBase prepare child W+1:=by
  rw[applyBlock_pc,tickAdvance_length,pc]
 have jump:=UniformMatchingAxisTableMachine.jump_runs (programFor prepare child W) B n 5 x
  (applyBlock tickAdvance s) (by rw[after];exact UniformGlobalClockPlacement.clock_backedge prepare child W)
  tick.final_bound (by omega)
 exact ⟨tick.trans jump,UniformGlobalClockControl.tick_headers s one⟩

theorem axis_branch {n B:ℕ} (prepare child:Program) (W:ℕ) (x:Fin n→ℂ) (s:State)
 (pc:s.pc=10) (wb:WordBound B s) (code:(programFor prepare child W).length ≤ B):
 BoundedRuns (programFor prepare child W) n x B s 1
  (setPC s (if s.natReg 5922 < s.natReg 5938 then 11 else kernelBase prepare)):=by
 have space:=control_space prepare child W code
 exact UniformMatchingAxisTableMachine.branch_runs _ B n 5922 5938 11 (kernelBase prepare) x s
  (by rw[pc];exact UniformGlobalClockPlacement.axis_branch prepare child W) wb space.2.2.2.2 space.2.2.1

theorem clock_branch {n B:ℕ} (prepare child:Program) (W:ℕ) (x:Fin n→ℂ) (s:State)
 (pc:s.pc=5) (wb:WordBound B s) (code:(programFor prepare child W).length ≤ B):
 BoundedRuns (programFor prepare child W) n x B s 1
  (setPC s (if s.natReg 5920 < s.natReg 5921 then 6 else finalPC prepare child W)):=by
 have space:=control_space prepare child W code
 exact UniformMatchingAxisTableMachine.branch_runs _ B n 5920 5921 6 (finalPC prepare child W) x s
  (by rw[pc];exact UniformGlobalClockPlacement.clock_branch prepare child W) wb (by omega) space.2.2.2.1

theorem halt_execution {n B:ℕ} (prepare child:Program) (W:ℕ) (x:Fin n→ℂ) (s:State)
 (pc:s.pc=finalPC prepare child W) (wb:WordBound B s):
 BoundedExecution (programFor prepare child W) n x B s 1 s:=
 .halt wb (by simp only[step,pc,UniformGlobalClockPlacement.halt_at])

lemma axis_kept (s:State) (j:ℕ) (kept:j≠5922 ∧j≠5923 ∧j≠5924 ∧j≠5925 ∧j≠5933):
 (setPC (applyBlock advance s) 10).natReg j=s.natReg j:=by
 simp only[advance,applyBlock,Op.apply,writeNat,next,setPC]
 simp only[Function.update_of_ne kept.1,Function.update_of_ne kept.2.1,
  Function.update_of_ne kept.2.2.1,Function.update_of_ne kept.2.2.2.1,Function.update_of_ne kept.2.2.2.2]

lemma tick_kept (s:State) (j:ℕ) (kept:j≠5920):
 (setPC (applyBlock tickAdvance s) 5).natReg j=s.natReg j:=by
 simp only[tickAdvance,applyBlock,Op.apply,writeNat,next,setPC,Function.update_of_ne kept]
end
end ExactFourierCircuits.UniformGlobalClockAdvanceExecution

import UniformActualTickRetention
import UniformGlobalClockAdvanceExecution

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalClockTickExecution
open UniformMachine UniformAssembly UniformKernelDiagonalBanks
open UniformTensorMonomialMachine (setPC applyBlock)
noncomputable section
attribute [local irreducible] Nat.add UniformGlobalClockConductor.programFor

/-- One synchronized numerical tick runs the actual corrected recursive
program, the charged tensor diagonal, and the actual clock increment/backedge.
The former recursive RootBody is discharged by the closed program proof. -/
theorem execution {F R n:ℕ}
 (prepare:Program)
 (g:Kernel (W:=UniformRecursiveSelfCallMachine.W) (F:=F) (R:=R))
 (d:Diagonal UniformRecursiveSelfCallMachine.W) (links:Links g d)
 (v:ℕ→Fin g.packing.volume→Scalar) (x:Fin n→ℂ) (s:State)
 (input:UniformKernelHeaderInstallation.Input g s)
 (diagonalInput:UniformDiagonalHeaderInstallation.Input d.rows d.tensor s)
 (banks:UniformGlobalRolePackingMachine.Banks g.packing g.physical s)
 (source:UniformGlobalRolePackingMachine.Source g.packing v s)
 (directory:UniformGlobalDiagonalRowsMachine.Directory d.rows.directory d.entries 0 s)
 (pools:UniformGlobalDiagonalRowsMachine.Pools d.entries s)
 (constants:UniformBinaryCStageMachine.Constants s)
 (reserve:UniformRecursiveReserve.reserve ≤ R)
 (positive:0 < UniformRecursiveSelfCallMachine.W)
 (code:(UniformGlobalClockConductor.programFor prepare UniformRecursiveSavingProgram.program
  UniformRecursiveSelfCallMachine.W).length ≤ g.metadata.B)
 (pc:s.pc=0) (wb:WordBound g.metadata.B s)
 (one:s.natReg 5939=1) (unfinished:s.natReg 5920 < s.natReg 5921):
 ∃u ticks,BoundedRuns
  (UniformGlobalClockConductor.programFor prepare UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W)
  n x g.metadata.B (placed (UniformGlobalClockConductor.kernelBase prepare) s) ticks u ∧
 ticks ≤ UniformGlobalKernelDiagonalRetention.budget g d UniformRecursiveChildInduction.cost+2 ∧u.pc=5 ∧
 u.natReg 5920=s.natReg 5920+1 ∧
 (∀r,r < UniformRecursiveSelfCallMachine.W→∀j:Fin d.packing.volume,
  (u.scalarHeap (d.tensor.source+r*d.tensor.volume+j.val)).map Scalar.value=
   some (UniformDiagonalReturnNumeric.multiplier d j*kernelValue g d links v r j)) ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,q < links.natEnd→q < d.rows.rows→q < d.rows.permutation→q < d.tensor.natStack→u.natHeap q=s.natHeap q) ∧
 (∀q,q < links.scalarEnd→q < d.rows.coefficient→q < d.tensor.scalarStack→q < d.tensor.source→
  q < d.tensor.destination→u.scalarHeap q=s.scalarHeap q) ∧
 (∀j,5920 ≤ j→j < 5940→j≠5920→u.natReg j=s.natReg j) ∧
 (∀j,(6000 ≤ j ∧j < 6200 ∨6300 ≤ j)→u.natReg j=s.natReg j) ∧
 (∀j,100 ≤ j→j < 107→u.natReg j=s.natReg j):=by
 have size:prepare.length+UniformRecursiveSavingProgram.program.length+1183 ≤ g.metadata.B:=by
  rwa[UniformGlobalClockConductor.program_length] at code
 obtain ⟨t,time,run,cheap,_tp,values,outputs,roots,nat,scalar,clock,high,startup⟩:=
  UniformActualTickRetention.execution g d links v x s input diagonalInput banks source directory pools constants
   reserve positive (by omega) pc wb
 have kernelSize:UniformGlobalClockConductor.kernelBase prepare+
  (UniformGlobalKernelDiagonalAssembly.programFor UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W).length ≤ g.metadata.B:=by
  rw[UniformGlobalKernelDiagonalAssembly.program_length]
  simp only[UniformGlobalClockConductor.kernelBase,UniformGlobalClockConductor.advanceBase,
   UniformGlobalClockConductor.adapterBase,UniformGlobalClockConductor.dispatchBase]
  omega
 have tickPC:UniformGlobalClockConductor.tickBase prepare UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W ≤ g.metadata.B:=by
  exact kernelSize
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed
  (UniformGlobalClockConductor.kernel_code prepare UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W)
  kernelSize tickPC run
 let middle:=setPC t (UniformGlobalClockConductor.tickBase prepare UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W)
 have middleOne:middle.natReg 5939=1:=(clock 5939 (by omega) (by omega)).trans one
 have middleUnfinished:middle.natReg 5920 < middle.natReg 5921:=by
  change t.natReg 5920 < t.natReg 5921
  rw[clock 5920 (by omega) (by omega),clock 5921 (by omega) (by omega)];exact unfinished
 obtain ⟨tick,advanced⟩:=UniformGlobalClockAdvanceExecution.tick_execution prepare UniformRecursiveSavingProgram.program
  UniformRecursiveSelfCallMachine.W x middle rfl middleOne placedRun.final_bound code middleUnfinished
 let u:=setPC (applyBlock UniformGlobalClockConductor.tickAdvance middle) 5
 have frame:=UniformGlobalClockControl.heap_frame middle UniformGlobalClockConductor.tickAdvance (Or.inr (Or.inr (Or.inr rfl)))
 refine ⟨u,time+2,placedRun.trans tick,by omega,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · exact advanced.trans (congrArg (fun q=>q+1) (clock 5920 (by omega) (by omega)))
 · intro r hr j;rw[show u.scalarHeap=t.scalarHeap from frame.2.1];exact values r hr j
 · exact frame.2.2.2.1.trans outputs
 · exact frame.2.2.2.2.trans roots
 · intro q a b c e;exact (congrFun frame.1 q).trans (nat q a b c e)
 · intro q a b c e f;exact (congrFun frame.2.1 q).trans (scalar q a b c e f)
 · intro j lo hi ne;exact (UniformGlobalClockAdvanceExecution.tick_kept middle j ne).trans (clock j lo hi)
 · intro j h;exact (UniformGlobalClockAdvanceExecution.tick_kept middle j (by rcases h with h|h <;>omega)).trans (high j h)
 · intro j lo hi;exact (UniformGlobalClockAdvanceExecution.tick_kept middle j (by omega)).trans (startup j lo hi)
end
end ExactFourierCircuits.UniformGlobalClockTickExecution

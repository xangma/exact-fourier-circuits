import UniformActualPreparedSectorRootBody
import UniformPreparedKernelDiagonal
set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualKernelPreparedTags
open UniformMachine UniformKernelDiagonalBanks
noncomputable section

/-- Unconditional collective prepared-tag preservation for the actual corrected
common-C kernel followed by147. Every recursive tag obligation is discharged. -/
theorem execution {F R n:ℕ}
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
 (reserve:UniformRecursiveReserve.reserve≤R)
 (prepared:∀r,r<UniformRecursiveSelfCallMachine.W→∀j:Fin g.packing.volume,(v r j).dependent=false)
 (positive:0<UniformRecursiveSelfCallMachine.W)
 (code:UniformRecursiveSavingProgram.program.length+813≤g.metadata.B) (pc:s.pc=0) (wb:WordBound g.metadata.B s):
 ∃u ticks,BoundedExecution
  (UniformGlobalKernelDiagonalAssembly.programFor UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W)
  n x g.metadata.B s ticks u ∧
 ticks≤UniformGlobalKernelDiagonalExecution.budget g d UniformRecursiveChildInduction.cost ∧
 u.pc=UniformRecursiveSavingProgram.program.length+812 ∧
 (∀r,r<UniformRecursiveSelfCallMachine.W→∀j:Fin d.packing.volume,
  (u.scalarHeap (d.tensor.source+r*d.tensor.volume+j.val)).map Scalar.dependent=some false) ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders:=
 UniformPreparedKernelDiagonal.execution g d links v x s input diagonalInput banks source directory pools constants
  (UniformActualPreparedSectorRootBody.root_body n g.inverse.layout.B F R x reserve)
  reserve prepared positive code pc wb

/-- The prepared output conclusion belongs to any actual halted execution of
that exact literal program, and thus joins the existing numerical/frame proof. -/
theorem of_execution {F R n ticks:ℕ}
 (g:Kernel (W:=UniformRecursiveSelfCallMachine.W) (F:=F) (R:=R))
 (d:Diagonal UniformRecursiveSelfCallMachine.W) (links:Links g d)
 (v:ℕ→Fin g.packing.volume→Scalar) (x:Fin n→ℂ) (s u:State)
 (input:UniformKernelHeaderInstallation.Input g s)
 (diagonalInput:UniformDiagonalHeaderInstallation.Input d.rows d.tensor s)
 (banks:UniformGlobalRolePackingMachine.Banks g.packing g.physical s)
 (source:UniformGlobalRolePackingMachine.Source g.packing v s)
 (directory:UniformGlobalDiagonalRowsMachine.Directory d.rows.directory d.entries 0 s)
 (pools:UniformGlobalDiagonalRowsMachine.Pools d.entries s)
 (constants:UniformBinaryCStageMachine.Constants s)
 (reserve:UniformRecursiveReserve.reserve≤R)
 (prepared:∀r,r<UniformRecursiveSelfCallMachine.W→∀j:Fin g.packing.volume,(v r j).dependent=false)
 (positive:0<UniformRecursiveSelfCallMachine.W)
 (code:UniformRecursiveSavingProgram.program.length+813≤g.metadata.B) (pc:s.pc=0) (wb:WordBound g.metadata.B s)
 (run:BoundedExecution
  (UniformGlobalKernelDiagonalAssembly.programFor UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W)
  n x g.metadata.B s ticks u):
 ∀r,r<UniformRecursiveSelfCallMachine.W→∀j:Fin d.packing.volume,
 (u.scalarHeap (d.tensor.source+r*d.tensor.volume+j.val)).map Scalar.dependent=some false:=by
 obtain ⟨z,time,actual,_cheap,_zp,tags,_outputs,_roots⟩:=
  execution g d links v x s input diagonalInput banks source directory pools constants reserve prepared positive code pc wb
 have same:u=z:=(run.executes.deterministic actual.executes).2
 subst u
 exact tags
end
end ExactFourierCircuits.UniformActualKernelPreparedTags

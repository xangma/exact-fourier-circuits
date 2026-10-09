import UniformGlobalKernelDiagonalExecution
import UniformActualSectorRootBody

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualKernelDiagonalExecution
open UniformMachine UniformKernelDiagonalBanks
noncomputable section

/-- The real corrected recursive program executes every common-C sector and
then the produced tensor diagonal. There is no recursive execution or desired
output premise: the root proof is discharged by the well-founded program proof. -/
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
 (reserve:UniformRecursiveReserve.reserve ≤ R)
 (positive:0 < UniformRecursiveSelfCallMachine.W)
 (code:UniformRecursiveSavingProgram.program.length+813 ≤ g.metadata.B)
 (pc:s.pc=0) (wb:WordBound g.metadata.B s):
 ∃u ticks,BoundedExecution
  (UniformGlobalKernelDiagonalAssembly.programFor UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W)
  n x g.metadata.B s ticks u ∧
 ticks ≤ UniformGlobalKernelDiagonalExecution.budget g d UniformRecursiveChildInduction.cost ∧
 u.pc=UniformRecursiveSavingProgram.program.length+812 ∧
 (∀r,r < UniformRecursiveSelfCallMachine.W→∀j:Fin d.packing.volume,
  (u.scalarHeap (d.tensor.source+r*d.tensor.volume+j.val)).map Scalar.value=
   some (UniformDiagonalReturnNumeric.multiplier d j*kernelValue g d links v r j)) ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders:=
 UniformGlobalKernelDiagonalExecution.execution g d links UniformRecursiveChildInduction.cost v x s input diagonalInput
  banks source directory pools constants (UniformActualSectorRootBody.root_body n g.inverse.layout.B F R x reserve)
  positive code pc wb
end
end ExactFourierCircuits.UniformActualKernelDiagonalExecution

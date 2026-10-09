import UniformGlobalClockTickExecution
import UniformKernelDiagonalTensorAction

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalTensorTickExecution
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
 (a:∀i:Fin (UniformKernelDiagonalTensorAction.physical g).length,
  Fin ((UniformKernelDiagonalTensorAction.physical g).get i).widths.sum→ℂ)
 (aligned:UniformKernelDiagonalTensorAction.Aligned g d a)
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
   some ((Matrix.reindex
    (UniformPhysicalTensorPi.coordinate (UniformKernelDiagonalTensorAction.physical g))
    (UniformPhysicalTensorPi.coordinate (UniformKernelDiagonalTensorAction.physical g))
    (OAI.ExactFourier.PiTensor.matrix (fun i:Fin (UniformKernelDiagonalTensorAction.physical g).length=>
     Matrix.diagonal (a i)*UniformMatchingKernelGeometry.localKernel
      ((UniformKernelDiagonalTensorAction.physical g).get i)))).mulVec
    (fun k=>(v r (finCongr g.physicalVolume k)).value)
    (finCongr (g.physicalVolume.trans links.volume).symm j))) ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,q < links.natEnd→q < d.rows.rows→q < d.rows.permutation→q < d.tensor.natStack→u.natHeap q=s.natHeap q) ∧
 (∀q,q < links.scalarEnd→q < d.rows.coefficient→q < d.tensor.scalarStack→q < d.tensor.source→
  q < d.tensor.destination→u.scalarHeap q=s.scalarHeap q) ∧
 (∀j,5920 ≤ j→j < 5940→j≠5920→u.natReg j=s.natReg j) ∧
 (∀j,(6000 ≤ j ∧j < 6200 ∨6300 ≤ j)→u.natReg j=s.natReg j) ∧
 (∀j,100 ≤ j→j < 107→u.natReg j=s.natReg j):=by
 obtain ⟨u,ticks,run,cost,pc',clock,values,outputs,roots,nat,scalar,kept,high,startup⟩:=
  UniformGlobalClockTickExecution.execution prepare g d links v x s input diagonalInput banks source directory pools
   constants reserve positive code pc wb one unfinished
 exact ⟨u,ticks,run,cost,pc',clock,UniformKernelDiagonalTensorAction.stored g d links a aligned v u values,
  outputs,roots,nat,scalar,kept,high,startup⟩
end
end ExactFourierCircuits.UniformGlobalTensorTickExecution

import UniformDiagonalReturnCore
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDiagonalReturnNumeric
open UniformMachine UniformTensorMonomialMachine
open UniformGlobalDiagonalChildPrefix (Context diagonalTicks phaseValues)
open UniformDiagonalReturnCore (Ready)
noncomputable section
/-- The multiplier is exactly the produced lane of each physical factor pool,
under the actual tensor traversal's mixed-radix coordinate. -/
def multiplier {W:ℕ} (c:Context W) (j:Fin c.packing.volume):ℂ:=
 tensorCoefficient (UniformGlobalDiagonalRowsMachine.axes c.lane c.rows.permutation c.rows.coefficient 0 c.entries)
  (finCongr (UniformGlobalTensorPackingBridge.output_volume c.packing c.tensor c.entries c.lane
   c.rows.permutation c.rows.coefficient c.volume c.tensorVolume) j)
lemma phase_value {W:ℕ} (c:Context W) (v:ℕ→ℕ→Scalar) (r:ℕ) (j:Fin c.packing.volume):
 (phaseValues c v r j).value=multiplier c j*(v r j.val).value:=rfl
/-- Actual147 has this diagonal numerical action; the coefficients are its
genuine produced pool values, and the stored tags are still those of execution. -/
theorem execution {W n:ℕ} (c:Context W) (v:ℕ→ℕ→Scalar) (x:Fin n→ℂ) (s:State)
 (ready:Ready c v s) (code:147≤c.metadata.B) (pc:s.pc=0) (wb:WordBound c.metadata.B s):
 ∃u,BoundedExecution (UniformGlobalDiagonalReturn.programFor W) n x c.metadata.B s
  (diagonalTicks c+7*(W*c.tensor.volume)+10) u ∧u.pc=146 ∧
 (∀r,r<W→∀j:Fin c.packing.volume,
  (u.scalarHeap (c.tensor.source+r*c.tensor.volume+j.val)).map Scalar.value=
   some ((Matrix.diagonal (multiplier c)).mulVec (fun k=>(v r k.val).value) j)) ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,q<c.rows.coefficient→q<c.tensor.scalarStack→q<c.tensor.source→q<c.tensor.destination→
  u.scalarHeap q=s.scalarHeap q) ∧
 (∀q,q<c.rows.rows→q<c.rows.permutation→q<c.tensor.natStack→u.natHeap q=s.natHeap q):=by
 obtain ⟨u,run,up,values,outputs,roots,scalar,nat⟩:=UniformDiagonalReturnCore.execution c v x s ready code pc wb
 refine ⟨u,run,up,?_,outputs,roots,scalar,nat⟩
 intro r hr j
 rw[values r hr j]
 simp only[Option.map_some,phase_value,Matrix.mulVec_diagonal]
end
end ExactFourierCircuits.UniformDiagonalReturnNumeric

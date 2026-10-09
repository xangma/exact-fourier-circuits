import UniformConditionalSectorLoop
import UniformRecursiveRootExecution
import UniformRecursiveStaticNatFrame

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualSectorRootBody
open UniformMachine
noncomputable section

/-- The proved actual recursive root closes the former sector-loop child
obligation. The reserve comparison is ordinary layout arithmetic; there is
no child execution, handler, prepared tape or transform premise. -/
theorem root_body (n B F reserve:ℕ) (x:Fin n→ℂ)
 (enough:UniformRecursiveReserve.reserve ≤ reserve):
 UniformConditionalSectorLoop.RootBody UniformRecursiveSavingProgram.program
  UniformRecursiveSelfCallMachine.W n B F reserve UniformRecursiveChildInduction.cost x:=by
 intro q A v s pc header depth source low extent room square code constants bound
 let input:Fin UniformRecursiveSelfCallMachine.W→Fin (2^q)→Scalar:=fun r j=>v r.val j.val
 have data:∀r j,s.scalarHeap (A+r.val*2^q+j.val)=some (input r j):=by
  intro r j
  exact source r.val r.isLt j.val j.isLt
 have room':F+34*(q+1)+UniformRecursiveReserve.reserve*(q+1)*2^q ≤ B:=by
  have small:=Nat.mul_le_mul_right (2^q) (Nat.mul_le_mul_right (q+1) enough)
  omega
 obtain ⟨u,ticks,run,time,values,nat,scalar,con,outputs,roots⟩:=UniformRecursiveRootExecution.execution
  n B q A F x input s pc header.exponent header.base header.width header.frontier depth data
  low extent (by omega) room' square constants bound
 refine ⟨u,ticks,run,time,?_,nat,scalar,?_,con,outputs,roots⟩
 · intro r hr j
   exact values ⟨r,hr⟩ j
 · intro j kept
   apply UniformRecursiveStaticNatFrame.bounded_execution_frame run j
   rcases kept with same|high
   · exact Or.inl same
   · exact Or.inr ⟨by omega,by omega⟩

end
end ExactFourierCircuits.UniformActualSectorRootBody

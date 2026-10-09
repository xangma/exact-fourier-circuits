import UniformRecursivePreparedChildInduction
import UniformRecursiveRootPackage
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveRootPackage
open UniformMachine UniformBinaryTensorCoordinates
namespace P
export UniformRecursiveSavingProgram (program address)
end P
namespace S
export UniformRecursiveSelfCallMachine (W)
end S
noncomputable section

def PreparedResult (n B k A F:ℕ)(cost:ℕ→ℕ)(x:Fin n→ℂ)
 (input:Fin S.W→Fin (2^k)→Scalar)(s:State):Prop:=∃u ticks,
 BoundedExecution P.program n x B s ticks u ∧ticks ≤ cost k ∧
 (∀(i:Fin S.W)(z:Fin (2^k)),(u.scalarHeap (A+i.val*2^k+z.val)).isSome=true ∧
  (u.scalarHeap (A+i.val*2^k+z.val)).map Scalar.value=
   some ((physicalMatrix k).mulVec (fun y=>(input i y).value) z)) ∧
 (∀z,z < F→u.natHeap z=s.natHeap z) ∧
 (∀z,z < F→(z < A∨A+S.W*2^k ≤ z)→u.scalarHeap z=s.scalarHeap z) ∧
 UniformBinaryCStageMachine.Constants u ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (UniformRecursivePreparedValues.Prepared2 input→∀(i:Fin S.W)(z:Fin (2^k)),
  (u.scalarHeap (A+i.val*2^k+z.val)).map Scalar.dependent=some false)

lemma finalize_prepared (n B k A F:ℕ)(cost:ℕ→ℕ)(x:Fin n→ℂ)
 (input:Fin S.W→Fin (2^k)→Scalar)(s u:State)(ticks:ℕ)
 (run:BoundedRuns P.program n x B s ticks u)(pc:u.pc=P.address .halt)
 (present:∀(i:Fin S.W)(z:Fin (2^k)),(u.scalarHeap (A+i.val*2^k+z.val)).isSome=true)
 (values:∀(i:Fin S.W)(z:Fin (2^k)),(u.scalarHeap (A+i.val*2^k+z.val)).map Scalar.value=
   some ((physicalMatrix k).mulVec (fun y=>(input i y).value) z))
 (nh:∀z,z < F→u.natHeap z=s.natHeap z)
 (sh:∀z,z < F→(z < A∨A+S.W*2^k ≤ z)→u.scalarHeap z=s.scalarHeap z)
 (constants:UniformBinaryCStageMachine.Constants u)(outputs:u.outputs=s.outputs)(roots:u.rootOrders=s.rootOrders)
 (time:ticks+1 ≤ cost k)
 (prepared:UniformRecursivePreparedValues.Prepared2 input→∀(i:Fin S.W)(z:Fin (2^k)),
  (u.scalarHeap (A+i.val*2^k+z.val)).map Scalar.dependent=some false):PreparedResult n B k A F cost x input s:=by
 have halt:BoundedExecution P.program n x B u 1 u:=.halt run.final_bound
  (by simp only [step,pc,UniformRecursiveSmallExecution.halt_code])
 exact ⟨u,ticks+1,run.executes halt,time,fun i z=>⟨present i z,values i z⟩,nh,sh,constants,outputs,roots,prepared⟩

end
end ExactFourierCircuits.UniformRecursiveRootPackage

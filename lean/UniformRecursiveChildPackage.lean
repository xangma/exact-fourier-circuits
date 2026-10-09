import UniformRecursiveGroupExecution
import UniformRecursiveSavingExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveChildPackage
open UniformMachine UniformBinaryTensorCoordinates
open UniformRecursiveGroupExecution (ChildBody)
namespace P
export UniformRecursiveSavingProgram (program address)
end P
namespace S
export UniformRecursiveSelfCallMachine (W)
end S
noncomputable section
lemma execution (n B k A F stack stackTop depth:ℕ)(cost:ℕ→ℕ)(x:Fin n→ℂ)
 (input g:Fin S.W→Fin (2^k)→Scalar)(s t u:State)(ticks:ℕ)
 (entry:BoundedRuns P.program n x B s 4 t)(run:BoundedRuns P.program n x B t ticks u)
 (pc:u.pc=P.address .returnSite)(sp:u.natReg 4150=stack)(dp:u.natReg 4151=depth)
 (out:∀i z,u.scalarHeap (A+i.val*2^k+z.val)=some (g i z))
 (values:∀i,(fun z=>(g i z).value)=(physicalMatrix k).mulVec (fun z=>(input i z).value))
 (nh:∀z,z < F→(z < stack+34*depth∨stackTop ≤ z)→u.natHeap z=t.natHeap z)
 (sh:∀z,z < F→(z < A∨A+S.W*2^k ≤ z)→u.scalarHeap z=t.scalarHeap z)
 (constants:UniformBinaryCStageMachine.Constants u)(outputs:u.outputs=t.outputs)(roots:u.rootOrders=t.rootOrders)
 (frame:UniformRecursiveSavingExecution.EntryFrame s t)(time:4+ticks ≤ cost k):
 ChildBody n B k A F stack stackTop depth cost x input s:=by
 refine ⟨u,4+ticks,entry.trans run,pc,sp,dp,?_,?_,?_,?_,constants,
  outputs.trans frame.outputs,roots.trans frame.roots,time⟩
 · intro i z;rw [out i z];rfl
 · intro i z
   rw [out i z,Option.map_some]
   exact congrArg some (congrFun (values i) z)
 · intro z hz away;exact (nh z hz away).trans (congrFun frame.natHeap z)
 · intro z hz away;exact (sh z hz away).trans (congrFun frame.scalarHeap z)
end
end ExactFourierCircuits.UniformRecursiveChildPackage

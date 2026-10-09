import UniformFourierAxisOperationalFrames
import UniformAxisBoundaryExecutionOutside

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisOperationalCases
open UniformMachine UniformJointAllocation UniformJointCacheAllocation
noncomputable section

/-- Every real389 branch preserves all Nat cells outside its own selection and
boundary interval. The boundary frame comes from its actual packing execution. -/
lemma Branch.natOutside{c:Constants}{n d g rectangleCount ticks:ℕ}{hn:0<n}{j:Fin (ell n)}
 {rectangle:ℕ→ℕ×ℕ}{nodes:List R.Range}{x:Fin n→ℂ}{s u:State}
 (input:Inputs c n d g rectangleCount j rectangle nodes x s)
 (capacity:rectangleCount+R.total nodes≤UniformJointCacheExtent.capacity (UniformAllAxisSeedPreparation.radix n j))
 (run:BoundedExecution UniformFourierAxisPrepareMachine.program n x (envelope c n) s ticks u)
 (actual:Branch c n d g rectangleCount hn j rectangle nodes x s u):
 ∀z,(z<(W.axis c n j).selected∨(W.axis c n j).phase≤z)→u.natHeap z=s.natHeap z:=by
 cases actual with
 | tree _ a=>exact tree_natOutside a capacity
 | boundary _ active _=>
  obtain ⟨v,t,q,real,_,_,outside⟩:=UniformAxisBoundaryExecutionOutside.execution_outside c hn j x s
   input.head input.later input.input input.natFrontier input.scalarFrontier input.epoch input.duration
   input.fit input.pc input.bound active input.pool input.physical input.directory
  have same:=(real.executes.deterministic run.executes).2
  subst u
  exact outside
 | inactive _ a=>exact fun z _=>congrFun a.frame.natHeap z

end
end ExactFourierCircuits.UniformFourierAxisOperationalCases

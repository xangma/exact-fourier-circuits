import UniformRecursiveLargeChild
import UniformRecursiveSmallBody
import UniformRecursiveTypedLargeCost
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveChildInduction
open UniformMachine UniformFixedNetwork
open UniformRecursiveGroupExecution (ChildBody SmallerBodies)
namespace P
export UniformRecursiveSavingProgram (program threshold seedPrinterLength unitPrinterLength size)
end P
namespace R
export UniformRecursiveReserve (reserve)
end R
noncomputable section

def cost:ℕ→ℕ:=UniformRecursiveRuntimeBridge.costWithUnit UniformRecursiveActualRuntime.stepUnit
lemma cap13 (named body cap:ℕ)(h:20+named+body ≤ cap):13+named+body ≤ cap:=by omega
lemma large_cost (q rest:ℕ)(large:P.threshold ≤ q*m+rest)(qp:1 ≤ q)(rp:rest < m):
 13+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady)+
 UniformRecursivePrintedBody.bodyTicks q rest cost ≤ cost (q*m+rest):=
 cap13 _ _ _ (UniformRecursiveTypedLargeCost.large_node_bound q rest qp rp large)

/-- Every positive-depth call executes the same fixed literal program. The
strict induction supplies its own smaller calls; no child action is assumed. -/
theorem execution (n B stack stackTop:ℕ)(x:Fin n→ℂ):
 ∀(k A F depth:ℕ)(input:Fin W→Fin (2^k)→Scalar)(s:State),
 s.pc=0→s.natReg 4120=k→s.natReg 4121=A→s.natReg 4122=2^k→s.natReg 4123=F→
 s.natReg 4150=stack→s.natReg 4151=depth→
 (∀(i:Fin W)(j:Fin (2^k)),s.scalarHeap (A+i.val*2^k+j.val)=some (input i j))→
 1 ≤ depth→3 ≤ A→A+W*2^k ≤ F→stack+34*(depth+k+1) ≤ stackTop→stackTop ≤ F→
 P.program.length ≤ B→F+R.reserve*(k+1)*2^k ≤ B→(2^k)^2 ≤ B→
 UniformBinaryCStageMachine.Constants s→WordBound B s→
 ChildBody n B k A F stack stackTop depth cost x input s:=by
 intro k
 induction k using Nat.strong_induction_on with
 | h k ih =>
  intro A F depth input s pc bits base size frontier sp dp data positive heapBase extent stackRoom stackEnd code room square constants bound
  by_cases small:k < P.threshold
  · exact UniformRecursiveSmallBody.execution n B k A F stack stackTop depth R.reserve x input s
     UniformRecursiveReserve.threshold_fit UniformRecursiveReserve.stack_fit small
     pc bits base size frontier sp dp data positive heapBase extent stackRoom stackEnd code room square constants bound
  · have large:P.threshold ≤ k:=by omega
    have childIH:SmallerBodies k n B R.reserve stack stackTop cost x:=by
     intro j hj
     exact ih j hj
    obtain ⟨qp,qlt,rp,form⟩:=UniformRecursiveSavingExecution.recursive_geometry k large
    generalize hq:k/ExplicitSeedBudget.m=q at qp qlt form
    generalize hr:k%ExplicitSeedBudget.m=rest at rp form
    have decomposition:k=q*m+rest:=form
    rw [decomposition] at bits
    clear form
    subst k
    exact UniformRecursiveLargeChild.execution n B A F q rest stack stackTop depth cost x input s childIH
     large qp rp qlt pc bits base size frontier sp dp data positive heapBase extent stackRoom stackEnd code room square constants bound
     (large_cost q rest large qp rp)

/-- The induction motive is now discharged for every parent exponent. -/
theorem smaller (parent n B stack stackTop:ℕ)(x:Fin n→ℂ):
 SmallerBodies parent n B R.reserve stack stackTop cost x:=by
 intro k _
 exact execution n B stack stackTop x k
end
end ExactFourierCircuits.UniformRecursiveChildInduction

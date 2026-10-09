import UniformRecursiveChildInduction
import UniformRecursivePreparedLargeChild
import UniformRecursivePreparedSmallBody
import UniformRecursiveTypedLargeCost

/-!
Paper correspondence: An explicit power saving for the exact discrete Fourier
transform, OpenAI math revision adc7f1241b42e322a6451854ab7e4b4c146bf78a,
§2.6, Theorem 2.6 proof, PDF pp. 11–12; §3.4, prepared-scalar discussion, p. 18.
The extra dependency-tag invariant is implementation bookkeeping: prepared inputs remain prepared through the same recursive execution. It is additional to the numerical matrix identity.
-/
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

/- Paper: Prepared-tag analogue of the same strict induction in Theorem 2.6, p. 11. No input-dependent branch or assumed child oracle is added by the stronger invariant. -/
theorem execution_prepared (n B stack stackTop:ℕ)(x:Fin n→ℂ):
 ∀(k A F depth:ℕ)(input:Fin W→Fin (2^k)→Scalar)(s:State),
 s.pc=0→s.natReg 4120=k→s.natReg 4121=A→s.natReg 4122=2^k→s.natReg 4123=F→
 s.natReg 4150=stack→s.natReg 4151=depth→
 (∀(i:Fin W)(j:Fin (2^k)),s.scalarHeap (A+i.val*2^k+j.val)=some (input i j))→
 1 ≤ depth→3 ≤ A→A+W*2^k ≤ F→stack+34*(depth+k+1) ≤ stackTop→stackTop ≤ F→
 P.program.length ≤ B→F+R.reserve*(k+1)*2^k ≤ B→(2^k)^2 ≤ B→
 UniformBinaryCStageMachine.Constants s→WordBound B s→
 UniformRecursiveGroupExecution.PreparedChildBody n B k A F stack stackTop depth cost x input s:=by
 intro k
 induction k using Nat.strong_induction_on with
 | h k ih =>
  intro A F depth input s pc bits base size frontier sp dp data positive heapBase extent stackRoom stackEnd code room square constants bound
  by_cases small:k < P.threshold
  · exact UniformRecursiveSmallBody.execution_prepared n B k A F stack stackTop depth R.reserve x input s
     UniformRecursiveReserve.threshold_fit UniformRecursiveReserve.stack_fit small
     pc bits base size frontier sp dp data positive heapBase extent stackRoom stackEnd code room square constants bound
  · have large:P.threshold ≤ k:=by omega
    have childIH:UniformRecursiveGroupExecution.PreparedSmallerBodies k n B R.reserve stack stackTop cost x:=by
     intro j hj
     exact ih j hj
    obtain ⟨qp,qlt,rp,form⟩:=UniformRecursiveSavingExecution.recursive_geometry k large
    generalize hq:k/ExplicitSeedBudget.m=q at qp qlt form
    generalize hr:k%ExplicitSeedBudget.m=rest at rp form
    have decomposition:k=q*m+rest:=form
    rw [decomposition] at bits
    clear form
    subst k
    exact UniformRecursiveLargeChild.execution_prepared n B A F q rest stack stackTop depth cost x input s childIH
     large qp rp qlt pc bits base size frontier sp dp data positive heapBase extent stackRoom stackEnd code room square constants bound
     (large_cost q rest large qp rp)

/-- The induction motive is now discharged for every parent exponent. -/
theorem smaller_prepared (parent n B stack stackTop:ℕ)(x:Fin n→ℂ):
 UniformRecursiveGroupExecution.PreparedSmallerBodies parent n B R.reserve stack stackTop cost x:=by
 intro k _
 exact execution_prepared n B stack stackTop x k
end
end ExactFourierCircuits.UniformRecursiveChildInduction

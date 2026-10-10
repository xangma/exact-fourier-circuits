import DFTModelSavingNativeLargeChild

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeChildInduction
open OAI.PowerSaving OAI.PowerSaving.RAM
open UniformMachine DFTModelAffine DFTModelAdmissibilityControl
open DFTModelSavingResidualNativeGroup
namespace P
export UniformRecursiveSavingProgram (program threshold)
end P
namespace R
export UniformRecursiveReserve (reserve)
end R
noncomputable abbrev cost := UniformRecursiveRuntimeBridge.costWithUnit UniformRecursiveActualRuntime.stepUnit
noncomputable section
attribute [local irreducible] P.program DFTModelSavingProgram.program R.reserve

lemma transfer (parent fuel n B stack stackTop : ℕ) (x : Fin n→ℂ) (enough : parent ≤ fuel+1)
    (before : PairSmallerBodies parent n B R.reserve stack stackTop cost x Complex.I
      (run DFTModelSavingProgram.program)) :
    PairSmallerBodies parent n B R.reserve stack stackTop cost x Complex.I
      (DFTModelSavingSelfCall.evaluate fuel) := by
  intro q smaller A F depth input input0 s s0 same pc bits base size fresh sp dp data data0 positive
    low endData roomStack endStack code room square constants bound
  obtain ⟨u,u0,ticks,actual,zero,matched,paired⟩:=before q smaller A F depth input input0 s s0
    same pc bits base size fresh sp dp data data0 positive low endData roomStack endStack code room square constants bound
  refine ⟨u,u0,ticks,actual,zero,matched,?_⟩
  have sameValue:=(DFTModelSavingSelfCall.fuel_closed_all q fuel (by omega) Complex.I
    (DFTModelRecursiveScalarSource.paired input input0)).1
  intro i j
  rw [sameValue]
  exact paired i j

/-- Every positive-depth call is an execution of the same fixed saving
program. Strong induction constructs its own smaller calls, and the one
closed typed run returns the exact actual/zero source Scalars together. -/
theorem execution (n B stack stackTop : ℕ) (x : Fin n→ℂ) :
    ∀(k A F depth : ℕ)(input input0 : Fin W→Fin (2^k)→Scalar)(s s0 : State),
      StateMatch s s0→s.pc=0→s.natReg 4120=k→s.natReg 4121=A→s.natReg 4122=2^k→s.natReg 4123=F→
      s.natReg 4150=stack→s.natReg 4151=depth→
      (∀(i : Fin W)(j : Fin (2^k)),s.scalarHeap (A+i.val*2^k+j.val)=some (input i j))→
      (∀(i : Fin W)(j : Fin (2^k)),s0.scalarHeap (A+i.val*2^k+j.val)=some (input0 i j))→
      1 ≤ depth→3 ≤ A→A+W*2^k ≤ F→stack+34*(depth+k+1) ≤ stackTop→stackTop ≤ F→
      P.program.length ≤ B→F+R.reserve*(k+1)*2^k ≤ B→(2^k)^2 ≤ B→
      UniformBinaryCStageMachine.Constants s→WordBound B s→
      ∃u u0 ticks,
        ChildResult n B k A F stack stackTop depth cost x input s u ticks ∧
        ChildResult n B k A F stack stackTop depth cost (fun _=>0) input0 s0 u0 ticks ∧
        StateMatch u u0 ∧
        ∀(i : Fin W)(j : Fin (2^k)),
          (run DFTModelSavingProgram.program ((k,Complex.I),DFTModelRecursiveScalarSource.paired input input0)).val.look
            (i.val*2^k+j.val) Tagged.blank=
            encodePaired ((u.scalarHeap (A+i.val*2^k+j.val)).getD Scalar.zero)
              ((u0.scalarHeap (A+i.val*2^k+j.val)).getD Scalar.zero) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih=>
    intro A F depth input input0 s s0 same pc bits base size frontier sp dp data data0 positive low endData
      roomStack endStack code room square constants bound
    by_cases small:k < P.threshold
    · obtain ⟨u,u0,ticks,actual,zero,matched,paired,_⟩:=DFTModelSavingNativeSmallBilledChild.execution
        n B k A F stack stackTop depth R.reserve x input input0 s s0 UniformRecursiveReserve.threshold_fit
        UniformRecursiveReserve.stack_fit small same pc bits base size frontier sp dp data data0 positive low
        endData roomStack endStack code room square constants bound
      exact ⟨u,u0,ticks,actual,zero,matched,paired⟩
    · have large:P.threshold ≤ k:=by omega
      have before:PairSmallerBodies k n B R.reserve stack stackTop cost x Complex.I
          (run DFTModelSavingProgram.program):=by
        intro q smaller
        exact ih q smaller
      have childIH:=transfer k (k-1) n B stack stackTop x (by omega) before
      obtain ⟨qp,qlt,rp,form⟩:=UniformRecursiveSavingExecution.recursive_geometry k large
      generalize hq:k/ExplicitSeedBudget.m=q at qp qlt form
      generalize hr:k%ExplicitSeedBudget.m=rest at rp form
      have decomposition:k=q*UniformFixedNetwork.m+rest:=form
      clear form
      cases decomposition
      exact DFTModelSavingNativeLargeChild.execution n B A F q rest stack stackTop depth x s s0 input input0
        childIH same large qp rp qlt pc bits base size frontier sp dp data data0 positive low endData
        roomStack endStack code room square constants bound

/-- No child callback remains: all smaller paired source executions are
supplied by the preceding strong induction. -/
theorem smaller (parent n B stack stackTop : ℕ) (x : Fin n→ℂ) :
    PairSmallerBodies parent n B R.reserve stack stackTop cost x Complex.I
      (run DFTModelSavingProgram.program) := by
  intro k _
  exact execution n B stack stackTop x k

end
end ExactFourierCircuits.DFTModelSavingNativeChildInduction

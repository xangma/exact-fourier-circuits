import DFTModelSavingResidualPaired
import DFTModelRecursiveScalarSource
import UniformRecursiveGroupLoop

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualNativeGroup
open UniformMachine UniformBinaryTensorCoordinates DFTModelAdmissibilityControl
open OAI.PowerSaving OAI.PowerSaving.RAM
open DFTModelAffine DFTModelSavingResidualSetup
namespace P
export UniformRecursiveSavingProgram (program address Part size)
end P
abbrev W := UniformRecursiveSelfCallMachine.W
noncomputable section
attribute [local irreducible] P.program UniformBatching.width

/-- The ordinary real positive-depth child postcondition, with its concrete
output state retained instead of existentially discarding its Scalar flags. -/
structure ChildResult (n B q A F stack stackTop depth : ℕ) (cost : ℕ → ℕ)
  (x : Fin n → ℂ) (input : Fin W → Fin (2^q) → Scalar) (s u : State) (ticks : ℕ) : Prop where
  run : BoundedRuns P.program n x B s ticks u
  pc : u.pc=P.address .returnSite
  stackReg : u.natReg 4150=stack
  depthReg : u.natReg 4151=depth
  present : ∀ (i : Fin W) (j : Fin (2^q)),(u.scalarHeap (A+i.val*2^q+j.val)).isSome=true
  values : ∀ (i : Fin W) (j : Fin (2^q)),(u.scalarHeap (A+i.val*2^q+j.val)).map Scalar.value=
    some ((physicalMatrix q).mulVec (fun z=>(input i z).value) j)
  nat : ∀z,z < F→(z < stack+34*depth∨stackTop ≤ z)→u.natHeap z=s.natHeap z
  scalar : ∀z,z < F→(z < A∨A+W*2^q ≤ z)→u.scalarHeap z=s.scalarHeap z
  constants : UniformBinaryCStageMachine.Constants u
  outputs : u.outputs=s.outputs
  roots : u.rootOrders=s.rootOrders
  time : ticks ≤ cost q

/-- Only the internal smaller-exponent induction hypothesis supplies this:
two genuine runs of the same RAM program, and one paired upstream child value.
No canonical flag fold or arbitrary numeric action replaces the actual outputs. -/
def PairSmallerBodies (parent n B reserve stack stackTop : ℕ) (cost : ℕ → ℕ)
  (x : Fin n → ℂ) (I : ℂ) (h : Handler DFTModelSavingResidual.Port) : Prop :=
  ∀q,q < parent→∀(A F depth : ℕ) (input input0 : Fin W → Fin (2^q) → Scalar) (s s0 : State),
  StateMatch s s0→s.pc=0→s.natReg 4120=q→s.natReg 4121=A→s.natReg 4122=2^q→s.natReg 4123=F→
  s.natReg 4150=stack→s.natReg 4151=depth→
  (∀(i : Fin W)(j : Fin (2^q)),s.scalarHeap (A+i.val*2^q+j.val)=some (input i j))→
  (∀(i : Fin W)(j : Fin (2^q)),s0.scalarHeap (A+i.val*2^q+j.val)=some (input0 i j))→
  1 ≤ depth→3 ≤ A→A+W*2^q ≤ F→stack+34*(depth+q+1) ≤ stackTop→stackTop ≤ F→
  P.program.length ≤ B→F+reserve*(q+1)*2^q ≤ B→(2^q)^2 ≤ B→
  UniformBinaryCStageMachine.Constants s→WordBound B s→
  ∃u u0 ticks,
    ChildResult n B q A F stack stackTop depth cost x input s u ticks ∧
    ChildResult n B q A F stack stackTop depth cost (fun _=>0) input0 s0 u0 ticks ∧
    StateMatch u u0 ∧
    ∀(i : Fin W)(j : Fin (2^q)),(h ((q,I),DFTModelRecursiveScalarSource.paired input input0)).val.look
      (i.val*2^q+j.val) Tagged.blank=
      encodePaired ((u.scalarHeap (A+i.val*2^q+j.val)).getD Scalar.zero)
        ((u0.scalarHeap (A+i.val*2^q+j.val)).getD Scalar.zero)

theorem boundedRuns_match {p : Program} {n B ticks : ℕ} {x y : Fin n → ℂ}
  {s s0 u : State} (run : BoundedRuns p n x B s ticks u) (same : StateMatch s s0) :
  ∃u0,BoundedRuns p n y B s0 ticks u0 ∧ StateMatch u u0 := by
  induction run generalizing s0 with
  | refl bound=>exact ⟨s0,.refl (same.wordBound bound),same⟩
  | next bound step tail ih=>
    obtain ⟨mid,step0,matched⟩:=step_match same step
    obtain ⟨u0,rest,last⟩:=ih matched
    exact ⟨u0,.next (same.wordBound bound) step0 rest,last⟩

theorem boundedRuns_unique {p : Program} {n B ticks : ℕ} {x : Fin n → ℂ}
  {s u v : State} (a : BoundedRuns p n x B s ticks u) (b : BoundedRuns p n x B s ticks v) : u=v := by
  induction a with
  | refl _=>cases b;rfl
  | next _ step tail ih=>
    cases b with
    | next _ step' rest=>
      have eq:=StepResult.running.inj (step.symm.trans step')
      subst eq
      exact ih rest

theorem constants_match {s s0 : State} (same : StateMatch s s0)
  (h : UniformBinaryCStageMachine.Constants s) : UniformBinaryCStageMachine.Constants s0 := by
  constructor
  · obtain ⟨z,hz,m⟩:=(same.scalarHeap 1).left h.1
    rw [←m.eq_of_prepared rfl] at hz
    exact hz
  · obtain ⟨z,hz,m⟩:=(same.scalarHeap 2).left h.2
    rw [←m.eq_of_prepared rfl] at hz
    exact hz

end
end ExactFourierCircuits.DFTModelSavingResidualNativeGroup

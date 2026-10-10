import DFTModelSavingResidualNativeGroupLoop

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualNativeGroup
open UniformMachine DFTModelAdmissibilityControl
open OAI.PowerSaving OAI.PowerSaving.RAM
open DFTModelAffine
noncomputable section
attribute [local irreducible] P.program UniformBatching.width

/-- The internal smaller-child premise additionally bills the one typed child
against the actual ticks of its witnessed source execution. -/
def BilledPairSmallerBodies (parent n B reserve stack stackTop K allowance : ℕ) (cost : ℕ → ℕ)
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
    (∀(i : Fin W)(j : Fin (2^q)),(h ((q,I),DFTModelRecursiveScalarSource.paired input input0)).val.look
      (i.val*2^q+j.val) Tagged.blank=
      encodePaired ((u.scalarHeap (A+i.val*2^q+j.val)).getD Scalar.zero)
        ((u0.scalarHeap (A+i.val*2^q+j.val)).getD Scalar.zero)) ∧
    (h ((q,I),DFTModelRecursiveScalarSource.paired input input0)).work ≤ K*ticks+allowance

theorem BilledPairSmallerBodies.forget
  {parent n B reserve stack stackTop K allowance : ℕ} {cost : ℕ → ℕ}
  {x : Fin n → ℂ} {I : ℂ} {h : Handler DFTModelSavingResidual.Port}
  (ih : BilledPairSmallerBodies parent n B reserve stack stackTop K allowance cost x I h) :
  PairSmallerBodies parent n B reserve stack stackTop cost x I h := by
  intro q smaller A F depth input input0 s s0 same pc bits base size fresh sp dp data data0 positive
    low endData roomStack endStack code room square constants bound
  obtain ⟨u,u0,ticks,run,run0,matched,paired,_⟩:=ih q smaller A F depth input input0 s s0 same pc
    bits base size fresh sp dp data data0 positive low endData roomStack endStack code room square constants bound
  exact ⟨u,u0,ticks,run,run0,matched,paired⟩

/-- Typed child work in the unvisited suffix of the physical group bank. -/
def remainingWork {groups : ℕ} (q : ℕ) (I : ℂ)
  (h : Handler DFTModelSavingResidual.Port)
  (input input0 : Fin groups → Fin W → Fin (2^q) → Scalar) (i : ℕ) : ℕ :=
  (((List.finRange groups).drop i).map fun g=>
    (h ((q,I),DFTModelRecursiveScalarSource.paired (input g) (input0 g))).work).sum

theorem remainingWork_done {groups : ℕ} (q : ℕ) (I : ℂ)
  (h : Handler DFTModelSavingResidual.Port)
  (input input0 : Fin groups → Fin W → Fin (2^q) → Scalar) :
  remainingWork q I h input input0 groups=0 := by
  unfold remainingWork
  rw [List.drop_of_length_le (by simp)]
  rfl

theorem remainingWork_step {groups : ℕ} (q : ℕ) (I : ℂ)
  (h : Handler DFTModelSavingResidual.Port)
  (input input0 : Fin groups → Fin W → Fin (2^q) → Scalar) {i : ℕ} (hi : i < groups) :
  remainingWork q I h input input0 i=
    (h ((q,I),DFTModelRecursiveScalarSource.paired (input ⟨i,hi⟩) (input0 ⟨i,hi⟩))).work+
      remainingWork q I h input input0 (i+1) := by
  have lookup : (List.finRange groups)[i]'(by simpa using hi)=⟨i,hi⟩ := by
    apply Fin.ext
    simp
  unfold remainingWork
  rw [List.drop_eq_getElem_cons (by simpa using hi),lookup]
  rfl

end
end ExactFourierCircuits.DFTModelSavingResidualNativeGroup

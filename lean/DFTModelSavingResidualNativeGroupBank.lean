import DFTModelSavingResidualNativeGroupPair

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualNativeGroup
open UniformMachine UniformBinaryTensorCoordinates DFTModelAdmissibilityControl
open OAI.PowerSaving OAI.PowerSaving.RAM
open DFTModelAffine DFTModelSavingResidualSetup
noncomputable section
attribute [local irreducible] P.program UniformBatching.width

/-- Completed physical groups retain the exact paired child output, including
its conservative flag. Unvisited groups retain both original Scalars. -/
structure PairBank (q groups D doneCount : ℕ) (I : ℂ)
  (h : Handler DFTModelSavingResidual.Port)
  (input input0 : Fin groups → Fin W → Fin (2^q) → Scalar) (s s0 : State) : Prop where
  actual : UniformRecursiveGroupLoop.Bank q groups D doneCount input s
  zero : UniformRecursiveGroupLoop.Bank q groups D doneCount input0 s0
  paired : ∀(g : Fin groups),g.val < doneCount→∀(j : Fin W)(t : Fin (2^q)),
    (h ((q,I),DFTModelRecursiveScalarSource.paired (input g) (input0 g))).val.look
      (j.val*2^q+t.val) Tagged.blank=
      encodePaired ((s.scalarHeap (D+g.val*(W*2^q)+j.val*2^q+t.val)).getD Scalar.zero)
        ((s0.scalarHeap (D+g.val*(W*2^q)+j.val*2^q+t.val)).getD Scalar.zero)

theorem PairBank.initial {q groups D : ℕ} {I : ℂ} {h : Handler DFTModelSavingResidual.Port}
  {input input0 : Fin groups → Fin W → Fin (2^q) → Scalar} {s s0 : State}
  (a : ∀(g : Fin groups)(j : Fin W)(t : Fin (2^q)),
    s.scalarHeap (D+g.val*(W*2^q)+j.val*2^q+t.val)=some (input g j t))
  (z : ∀(g : Fin groups)(j : Fin W)(t : Fin (2^q)),
    s0.scalarHeap (D+g.val*(W*2^q)+j.val*2^q+t.val)=some (input0 g j t)) :
  PairBank q groups D 0 I h input input0 s s0 :=
  ⟨.initial a,.initial z,fun _ impossible=>by omega⟩

theorem PairBank.withPC {q groups D doneCount : ℕ} {I : ℂ} {h : Handler DFTModelSavingResidual.Port}
  {input input0 : Fin groups → Fin W → Fin (2^q) → Scalar} {s s0 : State}
  (bank : PairBank q groups D doneCount I h input input0 s s0) (pc : ℕ) :
  PairBank q groups D doneCount I h input input0 {s with pc:=pc} {s0 with pc:=pc} :=
  ⟨bank.actual.withPC pc,bank.zero.withPC pc,bank.paired⟩

theorem PairBank.advance {n B k q m r D V A i groups F stack depth stackTop : ℕ}
  {cost : ℕ → ℕ} {x : Fin n → ℂ} {I : ℂ} {h : Handler DFTModelSavingResidual.Port}
  {input input0 : Fin groups → Fin W → Fin (2^q) → Scalar} {s s0 u u0 : State} {ticks : ℕ}
  (bank : PairBank q groups D i I h input input0 s s0)
  (hi : i < groups) (partition : groups*(W*2^q)=V) (dataEnd : D+V ≤ F)
  (a : GroupResult n B k q m r D V A i groups F stack depth stackTop cost x (input ⟨i,hi⟩) s u ticks)
  (z : GroupResult n B k q m r D V A i groups F stack depth stackTop cost (fun _=>0) (input0 ⟨i,hi⟩) s0 u0 ticks)
  (pair : ∀(j : Fin W)(t : Fin (2^q)),
    (h ((q,I),DFTModelRecursiveScalarSource.paired (input ⟨i,hi⟩) (input0 ⟨i,hi⟩))).val.look
      (j.val*2^q+t.val) Tagged.blank=
      encodePaired ((u.scalarHeap (D+i*(W*2^q)+j.val*2^q+t.val)).getD Scalar.zero)
        ((u0.scalarHeap (D+i*(W*2^q)+j.val*2^q+t.val)).getD Scalar.zero)) :
  PairBank q groups D (i+1) I h input input0 u u0 := by
  refine ⟨bank.actual.advance hi partition dataEnd a.present a.values a.scalar,
    bank.zero.advance hi partition dataEnd z.present z.values z.scalar,?_⟩
  intro g processed j t
  by_cases eq : g.val=i
  · have same : g=⟨i,hi⟩ := Fin.ext eq
    subst g
    exact pair j t
  · have below := (UniformRecursiveGroupLoop.point_in_bank partition g j t).trans_le dataEnd
    have outside := UniformRecursiveGroupLoop.other_group (D:=D) g j t eq
    rw [a.scalar _ below outside,z.scalar _ below outside]
    exact bank.paired g (by omega) j t

end
end ExactFourierCircuits.DFTModelSavingResidualNativeGroup

import DFTModelSavingResidualNativeGroupGeometry
import UniformRecursiveResidualFiberValues

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualNativeGroup
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine BinaryFrames DFTModelAffine DFTModelSavingResidualSetup
noncomputable section
attribute [local irreducible] UniformBatching.width DFTModelResidualClosedRole.gather

/-- Extensional tape equality uses only physical finite reads and length. -/
theorem tape_eq {α : Type} (a b : Tape α) (blank : α) (len : a.len=b.len)
  (reads : ∀j,j < a.len → a.look j blank=b.look j blank) : a=b := by
  cases a with
  | mk al ap=>
    cases b with
    | mk bl bp=>
      change al=bl at len
      subst bl
      congr 1
      funext j
      simpa only [Tape.look,j.isLt,↓reduceDIte] using reads j.val j.isLt

/-- The child's one complete-W tape is exactly the paired encoding of the
same physical first-pivot fiber batch, in the source's representative order. -/
theorem sliced_first {R : ℕ} (q w r : ℕ) (v : Vec (Fin (w+1))) (raw : Tape ℕ)
  (a : Fin R) (X X0 : Fin R → Fin (2^(q*(w+1)+r)) → Scalar) (qp : 1 ≤ q)
  (source : ∀i : Fin (w+1),raw.look i.val 0=(v i).val)
  (p : Fin (w+1)) (hp : v p=1) (before : ∀i : Fin (w+1),i.val < p.val → v i=0)
  (fits : ExplicitSeedBudget.roleBits ≤ q*w+r)
  (g : Fin (UniformRecursiveBatchGroupMachine.groupCount q w r)) :
  DFTModelClockBatch.sliced (W*2^q) g.val
    (run (DFTModelResidualClosedRole.gather Tagged)
      ((q,(w+1,(r,raw))),(a.val,DFTModelRecursiveScalarSource.paired X X0))).val.2.2 Tagged.blank=
    DFTModelRecursiveScalarSource.paired
      (UniformRecursiveResidualFiberValues.input q w r fits v p hp (X a) g)
      (UniformRecursiveResidualFiberValues.input q w r fits v p hp (X0 a) g) := by
  obtain ⟨length,gather⟩:=gather_first q w r a.val v raw (DFTModelRecursiveScalarSource.paired X X0)
    qp source p hp before
  refine tape_eq _ _ Tagged.blank ?_ ?_
  · rfl
  intro j hj
  change j < W*2^q at hj
  let ij := (finProdFinEquiv : Fin W×Fin (2^q)≃Fin (W*2^q)).symm ⟨j,hj⟩
  have val : j=ij.1.val*2^q+ij.2.val := by
    have eq := congrArg Fin.val ((finProdFinEquiv : Fin W×Fin (2^q)≃Fin (W*2^q)).apply_symm_apply ⟨j,hj⟩)
    have pairValue := UniformRecursiveResidualFiberValues.representative_value_generic W (2^q) (W*2^q) rfl ij.1 ij.2
    change (finProdFinEquiv (ij.1,ij.2)).val=ij.1.val*2^q+ij.2.val at pairValue
    exact eq.symm.trans pairValue
  let flat := UniformRecursiveGroupBank.flatten _ W (2^q) (2^(q*(w+1)+r))
    (UniformRecursiveBatchGroupMachine.partition q w r fits) (g,ij)
  have flatval : flat.val=g.val*(W*2^q)+j := by
    have f := UniformRecursiveGroupBank.flatten_value
      (UniformRecursiveBatchGroupMachine.groupCount q w r) W (2^q) (2^(q*(w+1)+r))
      (UniformRecursiveBatchGroupMachine.partition q w r fits) g ij.1 ij.2
    change flat.val=g.val*(W*2^q)+ij.1.val*2^q+ij.2.val at f
    omega
  have fiber : DFTModelResidualBasisGeometry.permutation q w r v p hp flat=
    UniformResidualExtendedPermutation.fibers q w r v p hp
      (UniformRecursiveResidualFiberValues.representative q w r fits (g,ij.1),ij.2) := by
    have f := UniformRecursiveResidualFiberValues.flatten_fiber q w r fits g ij.1 ij.2
    change flat=_ at f
    rw [f]
    exact UniformResidualExtendedPermutation.fibers_flat q w r v p hp _ _
  change (Tape.tab (W*2^q) _).look j Tagged.blank=_
  rw [Tape.look_of_lt _ _ hj]
  change (run (DFTModelResidualClosedRole.gather Tagged)
    ((q,(w+1,(r,raw))),(a.val,DFTModelRecursiveScalarSource.paired X X0))).val.2.2.look
    (g.val*(W*2^q)+j) Tagged.blank=(DFTModelRecursiveScalarSource.paired
    (UniformRecursiveResidualFiberValues.input q w r fits v p hp (X a) g)
    (UniformRecursiveResidualFiberValues.input q w r fits v p hp (X0 a) g)).look j Tagged.blank
  rw [gather ⟨g.val*(W*2^q)+j,by rw [←flatval];exact flat.isLt⟩]
  have flatEq : (⟨g.val*(W*2^q)+j,by rw [←flatval];exact flat.isLt⟩:Fin (2^(q*(w+1)+r)))=flat := Fin.ext flatval.symm
  rw [flatEq,fiber,DFTModelRecursiveScalarSource.paired_lookup]
  have outRead := DFTModelRecursiveScalarSource.paired_lookup
    (UniformRecursiveResidualFiberValues.input q w r fits v p hp (X a) g)
    (UniformRecursiveResidualFiberValues.input q w r fits v p hp (X0 a) g) ij.1 ij.2
  have outRead' := (congrArg (fun z=>(DFTModelRecursiveScalarSource.paired
    (UniformRecursiveResidualFiberValues.input q w r fits v p hp (X a) g)
    (UniformRecursiveResidualFiberValues.input q w r fits v p hp (X0 a) g)).look z Tagged.blank) val).trans outRead
  exact outRead'.symm

end
end ExactFourierCircuits.DFTModelSavingResidualNativeGroup

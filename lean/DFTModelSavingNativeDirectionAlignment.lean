import DFTModelSavingNativeDirectionTail

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeDirection
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelSavingResidualSetup
open DFTModelSavingResidualAction UniformResidualExtendedPermutation
noncomputable section
attribute [local irreducible] UniformBatching.width DFTModelSavingResidual.program
  DFTModelResidualClosedRole.gather

/-- The source's low-bit XOR and the typed local reflection select exactly
one and the same physical returned Scalar. -/
theorem selected_index (q w r : ℕ) (inv : Bool)
  (f : Fin (2^(q*(w+1)+r))→Scalar) (j : Fin (2^(q*(w+1)+r))) :
  UniformRecursiveResidualOutput.selected (q*(w+1)+r) q (by nlinarith) inv f j=
    f ⟨effectiveIndex (2^q) inv j.val,
      effectiveIndex_lt _ _ _ _ (Nat.two_pow_pos _) (size_divides q w r) j.isLt⟩ := by
  obtain ⟨⟨b,t⟩,rfl⟩:=(flat q w r).surjective j
  cases inv
  · rfl
  · simp only [UniformRecursiveResidualOutput.selected,ite_true]
    rw [UniformRecursiveResidualFiberValues.selected_flat q w r (by nlinarith) b t]
    congr 1
    apply Fin.ext
    change (flat q w r (b,UniformBinaryXorCoordinates.xorIndex t (UniformPhysicalBinaryInverse.mask q))).val=
      effectiveIndex (2^q) true (flat q w r (b,t)).val
    rw [flat_value,DFTModelSavingResidualNative.index_flat]
    rfl

/-- Complete physical output witnesses identify the one paired typed node.
The premises are concrete scatter reads and retained spectator cells. -/
theorem node_value {R : ℕ} (h : Handler DFTModelSavingResidual.Port) (q w r D k : ℕ)
  (v : BinaryFrames.Vec (Fin (w+1))) (raw : Tape ℕ) (a : Fin R) (I : ℂ) (inverse : Bool)
  (X X0 Y Y0 : Fin R→Fin (2^(q*(w+1)+r))→Scalar) (qp : 1≤q)
  (source : ∀i:Fin (w+1),raw.look i.val 0=(v i).val) (hv : BinaryFrames.dot v v=1)
  (p : Fin (w+1)) (hp : v p=1) (before : ∀i:Fin (w+1),i.val<p.val→v i=0)
  (fits : ExplicitSeedBudget.roleBits≤q*w+r) (u u0 : State)
  (bank : DFTModelSavingResidualNativeGroup.PairBank q (BG.groupCount q w r) D (BG.groupCount q w r) I h
    (FV.input q w r fits v p hp (X a)) (FV.input q w r fits v p hp (X0 a)) u u0)
  (scatter : ∀j,Y a (DFTModelResidualBasisGeometry.permutation q w r v p hp j)=
    UniformRecursiveResidualOutput.selected (q*(w+1)+r) q (by nlinarith)
      (UniformResidualFibers.inverseOrientation v inverse) (UniformRecursiveGroupBank.array D (2^(q*(w+1)+r)) u) j)
  (scatter0 : ∀j,Y0 a (DFTModelResidualBasisGeometry.permutation q w r v p hp j)=
    UniformRecursiveResidualOutput.selected (q*(w+1)+r) q (by nlinarith)
      (UniformResidualFibers.inverseOrientation v inverse) (UniformRecursiveGroupBank.array D (2^(q*(w+1)+r)) u0) j)
  (kept : ∀i,i≠a→∀j,Y i j=X i j) (kept0 : ∀i,i≠a→∀j,Y0 i j=X0 i j) :
  (Code.run DFTModelSavingResidual.program h ((q,(w+1,(r,raw))),
    (a.val,(UniformResidualOrientationArithmetic.boolCode inverse,((k,I),DFTModelRecursiveScalarSource.paired X X0))))).val=
    ((k,I),DFTModelRecursiveScalarSource.paired Y Y0) := by
  have room : a.val*2^(q*(w+1)+r)+2^(q*(w+1)+r)≤(DFTModelRecursiveScalarSource.paired X X0).len := by
    change a.val*2^(q*(w+1)+r)+2^(q*(w+1)+r)≤R*2^(q*(w+1)+r)
    calc
      _=(a.val+1)*2^(q*(w+1)+r) := by ring
      _≤R*2^(q*(w+1)+r) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt a.isLt)
  have preserved:=DFTModelSavingResidualGeometry.preserved h (q,(w+1,(r,raw))) a.val
    (UniformResidualOrientationArithmetic.boolCode inverse) k I (DFTModelRecursiveScalarSource.paired X X0)
  apply Prod.ext preserved.1
  apply DFTModelSavingResidualNativeGroup.tape_eq _ _ Tagged.blank
  · exact preserved.2
  intro z hz
  have small : z<R*2^(q*(w+1)+r) := by rw [preserved.2] at hz;exact hz
  let ij := (finProdFinEquiv : Fin R×Fin (2^(q*(w+1)+r))≃Fin (R*2^(q*(w+1)+r))).symm ⟨z,small⟩
  have value : z=ij.1.val*2^(q*(w+1)+r)+ij.2.val := by
    have back:=congrArg Fin.val ((finProdFinEquiv : Fin R×Fin (2^(q*(w+1)+r))≃
      Fin (R*2^(q*(w+1)+r))).apply_symm_apply ⟨z,small⟩)
    have flat:=UniformRecursiveResidualFiberValues.representative_value_generic R (2^(q*(w+1)+r))
      (R*2^(q*(w+1)+r)) rfl ij.1 ij.2
    change (finProdFinEquiv (ij.1,ij.2)).val=ij.1.val*2^(q*(w+1)+r)+ij.2.val at flat
    exact back.symm.trans flat
  rw [value,DFTModelRecursiveScalarSource.paired_lookup]
  by_cases eq : ij.1=a
  · rw [eq]
    obtain ⟨j,same⟩:=(DFTModelResidualBasisGeometry.permutation q w r v p hp).surjective ij.2
    rw [←same,endpoint_paired h q w r D k v raw a I inverse X X0 qp source hv p hp before fits u u0 bank j,
      scatter j,scatter0 j,selected_index,selected_index]
    rfl
  · obtain ⟨_,_,outside⟩:=endpoint_first h q w r v raw a.val k I inverse
      (DFTModelRecursiveScalarSource.paired X X0) qp source hv fits room p hp before
    have live : ij.1.val*2^(q*(w+1)+r)+ij.2.val<(DFTModelRecursiveScalarSource.paired X X0).len := by
      change _<R*2^(q*(w+1)+r)
      rw [←value]
      exact small
    have away : ¬(a.val*2^(q*(w+1)+r) ≤ ij.1.val*2^(q*(w+1)+r)+ij.2.val ∧
      ij.1.val*2^(q*(w+1)+r)+ij.2.val < a.val*2^(q*(w+1)+r)+2^(q*(w+1)+r)) := by
      have outsideRole:=UniformFixedNetworkShearChildMachine.role_outside 0 a ij.1 eq ij.2
      simp only [UniformFixedNetworkShearChildMachine.roleBase,Nat.zero_add] at outsideRole
      rcases outsideRole with less|more
      · omega
      · omega
    rw [outside ⟨_,live⟩ away,DFTModelRecursiveScalarSource.paired_lookup,kept _ eq,kept0 _ eq]

end
end ExactFourierCircuits.DFTModelSavingNativeDirection

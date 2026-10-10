import DFTModelSavingResidualNativeGroupDeterminism

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualNativeGroup
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open BinaryFrames UniformBinaryXorCoordinates
open DFTModelAffine DFTModelSavingResidualSetup
noncomputable section
attribute [local irreducible] UniformBatching.width DFTModelSavingResidual.program
  DFTModelResidualClosedAddresses.program DFTModelResidualClosedRole.gather
  DFTModelResidualBasisImages.program DFTModelResidualClosedBasis.parameters

/-- A physical least pivot identifies the charged typed pivot exactly. -/
theorem parameters_first (q w r : ℕ) (v : Vec (Fin (w+1))) (raw : Tape ℕ)
  (source : ∀i : Fin (w+1),raw.look i.val 0=(v i).val)
  (p : Fin (w+1)) (hp : v p=1) (before : ∀i : Fin (w+1),i.val < p.val→v i=0) :
  (run DFTModelResidualClosedBasis.parameters (q,(w+1,(r,raw)))).val=
    (q,(w+1,(r,((encode v).val,p.val)))) := by
  have point : raw.look p.val 0=1 := by rw [source p,hp];rfl
  have prior : ∀i,i < p.val → raw.look i 0=0 := by
    intro i hi
    rw [source ⟨i,hi.trans p.isLt⟩,before ⟨i,hi.trans p.isLt⟩ hi]
    rfl
  rw [DFTModelResidualClosedBasis.parameters_value,
    DFTModelResidualBasisMask.source_value (w+1) v raw source,
    DFTModelResidualBasisPivot.program_value (w+1) raw p.val p.isLt point prior]

theorem addresses_first (q w r : ℕ) (v : Vec (Fin (w+1))) (raw : Tape ℕ) (qp : 1 ≤ q)
  (source : ∀i : Fin (w+1),raw.look i.val 0=(v i).val)
  (p : Fin (w+1)) (hp : v p=1) (before : ∀i : Fin (w+1),i.val < p.val→v i=0) :
  (run DFTModelResidualClosedAddresses.program (q,(w+1,(r,raw)))).val.len=2^(q*(w+1)+r) ∧
  ∀j : Fin (2^(q*(w+1)+r)),
    (run DFTModelResidualClosedAddresses.program (q,(w+1,(r,raw)))).val.look j.val 0=
      (DFTModelResidualBasisGeometry.permutation q w r v p hp j).val := by
  let images := (run DFTModelResidualBasisImages.program
    (q,(w+1,(r,((encode v).val,p.val))))).val
  have imageBank : ∀i : Fin (q*(w+1)+r),images.look i.val 0=
    (DFTModelResidualBasisGeometry.permutation q w r v p hp (encode (unit i))).val :=
    DFTModelResidualBasisGeometry.program_images q w r v p hp
  have cover : q*(w+1)+r ≤ q*((w+1)+r) := by nlinarith
  have small : ∀i,i < q*(w+1)+r → images.look i 0 < 2^(q*((w+1)+r)) := by
    intro i hi
    rw [imageBank ⟨i,hi⟩]
    exact (Fin.isLt _).trans_le (Nat.pow_le_pow_right (by decide) cover)
  have value : (run DFTModelResidualClosedAddresses.program (q,(w+1,(r,raw)))).val=
    DFTModelResidualAddresses.reference images (q*(w+1)+r) := by
    rw [DFTModelResidualClosedAddresses.program_value q (w+1) r _ _ raw
      (parameters_first q w r v raw source p hp before),
      DFTModelResidualAddresses.program_value q ((w+1)+r) (q*(w+1)+r) images small]
  refine ⟨by rw [value];rfl,?_⟩
  intro j
  rw [value]
  have native := UniformResidualPermutation.address_of_xor_equiv
    (DFTModelResidualBasisGeometry.permutation q w r v p hp)
    (DFTModelResidualBasisGeometry.zero q w r v p hp)
    (DFTModelResidualBasisGeometry.xor q w r v p hp)
    (fun i=>images.look i 0) imageBank (q*(w+1)+r) 0 j.val le_rfl j.isLt
  simpa only [DFTModelResidualAddresses.reference,Tape.look,Tape.tab,j.isLt,↓reduceDIte,Nat.zero_xor] using native

theorem first_unique {w : ℕ} {v : Vec (Fin (w+1))} {p p0 : Fin (w+1)}
  (hp : v p=1) (hp0 : v p0=1)
  (before : ∀i : Fin (w+1),i.val < p.val→v i=0)
  (before0 : ∀i : Fin (w+1),i.val < p0.val→v i=0) : p=p0 := by
  apply Fin.ext
  rcases lt_trichotomy p.val p0.val with less|eq|more
  · have no := (before0 p less).symm.trans hp
    have : (0 : ZMod 2)≠1 := by decide
    exact False.elim (this no)
  · exact eq
  · have no := (before p0 more).symm.trans hp0
    have : (0 : ZMod 2)≠1 := by decide
    exact False.elim (this no)

theorem gather_first (q w r a : ℕ) (v : Vec (Fin (w+1))) (raw : Tape ℕ) (bank : Tape Tagged.T) (qp : 1 ≤ q)
  (source : ∀i : Fin (w+1),raw.look i.val 0=(v i).val)
  (p : Fin (w+1)) (hp : v p=1) (before : ∀i : Fin (w+1),i.val < p.val→v i=0) :
  (run (DFTModelResidualClosedRole.gather Tagged) ((q,(w+1,(r,raw))),(a,bank))).val.2.2.len=2^(q*(w+1)+r) ∧
  ∀j : Fin (2^(q*(w+1)+r)),
    (run (DFTModelResidualClosedRole.gather Tagged) ((q,(w+1,(r,raw))),(a,bank))).val.2.2.look j.val Tagged.blank=
      bank.look (a*2^(q*(w+1)+r)+(DFTModelResidualBasisGeometry.permutation q w r v p hp j).val) Tagged.blank := by
  obtain ⟨len,table⟩:=addresses_first q w r v raw qp source p hp before
  refine ⟨?_,?_⟩
  · rw [DFTModelResidualClosedRole.gather_value,DFTModelResidualMovement.gather_value]
    exact len
  · intro j
    rw [DFTModelResidualClosedRole.gathered_lookup Tagged _ a bank _ len j
      (by rw [table j];exact Fin.isLt _),table j]

end
end ExactFourierCircuits.DFTModelSavingResidualNativeGroup

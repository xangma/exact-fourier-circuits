import DFTModelSavingResidualAction
import UniformRecursiveResidualDirectionLoop

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualNative
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open BinaryFrames UniformBinaryXorCoordinates UniformBinaryTensorCoordinates
open UniformResidualExtendedPermutation UniformResidualNativeCoordinates
open UniformNativeResidualSemantics UniformNativeCopiedInverse
open DFTModelSavingResidualAction
noncomputable section

def signedMatrix (q w r : ℕ) (v : Vec (Fin (w+1))) (hv : dot v v=1) (inverse : Bool) :=
  spectatorMatrix (q*(w+1)) r (nativeWordMatrix (UniformResidualFibers.signedColumnWord q v hv inverse))

theorem mask_complement (q : ℕ) (t : Fin (2^q)) :
  (xorIndex t (UniformPhysicalBinaryInverse.mask q)).val=2^q-1-t.val := by
  change t.val^^^(UniformPhysicalBinaryInverse.mask q).val=_
  rw [UniformPhysicalBinaryInverse.mask_value]
  have eq:=congrArg BitVec.toNat (BitVec.xor_allOnes (x:=BitVec.ofNat q t.val))
  simpa only [BitVec.toNat_xor,BitVec.toNat_allOnes,BitVec.toNat_not,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt t.isLt] using eq

theorem index_flat (q w r : ℕ) (inverse : Bool) (b : Fin (2^(q*w+r))) (t : Fin (2^q)) :
  effectiveIndex (2^q) inverse (flat q w r (b,t)).val=
    b.val*2^q+(if inverse then xorIndex t (UniformPhysicalBinaryInverse.mask q) else t).val := by
  rw [flat_value]
  cases inverse
  · rfl
  · change DFTModelSavingResidualFlip.index (2^q) (b.val*2^q+t.val)=_
    simp only [ite_true]
    rw [DFTModelSavingResidualFlip.index,mask_complement]
    rw [Nat.add_comm (b.val*2^q) t.val,Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt t.isLt,Nat.zero_add,Nat.add_mod,Nat.mul_mod_left,Nat.mod_eq_of_lt t.isLt]
    simp only [Nat.mod_eq_of_lt t.isLt,Nat.add_zero]

 theorem signed_fibers (q w r : ℕ) (v : Vec (Fin (w+1))) (hv : dot v v=1)
  (p : Fin (w+1)) (hp : v p=1) (inverse : Bool)
  (X : Fin (2^(q*(w+1)+r)) → ℂ) (b : Fin (2^(q*w+r))) (t : Fin (2^q)) :
  (signedMatrix q w r v hv inverse).mulVec X (fibers q w r v p hp (b,t))=
    (physicalMatrix q).mulVec (fun s=>X (fibers q w r v p hp (b,s)))
      (if UniformResidualFibers.inverseOrientation v inverse then
        xorIndex t (UniformPhysicalBinaryInverse.mask q) else t) := by
  simpa only [signedMatrix,fibers,UniformResidualSpectators.split,spectatorSplit,
    Equiv.trans_apply,Equiv.prodCongr_apply,Equiv.refl_apply,Equiv.prodAssoc_apply,Prod.map]
    using native_signed_spectator_array q w r v hv p hp inverse X
      ((UniformResidualSpectators.split (q*w) r b).1)
      ((UniformResidualSpectators.split (q*w) r b).2) t

 theorem fiber_formula (q w r : ℕ) (v : Vec (Fin (w+1))) (hv : dot v v=1)
  (p : Fin (w+1)) (hp : v p=1) (inverse : Bool)
  (X : Fin (2^(q*(w+1)+r)) → ℂ) (j : Fin (2^(q*(w+1)+r))) :
    (physicalMatrix q).mulVec
      (fun s=>X (DFTModelResidualBasisGeometry.permutation q w r v p hp
        ⟨effectiveIndex (2^q) (UniformResidualFibers.inverseOrientation v inverse) j.val/2^q*2^q+s.val,
          block_lt _ _ _ _ (Nat.two_pow_pos _) (size_divides q w r)
            (effectiveIndex_lt _ _ _ _ (Nat.two_pow_pos _) (size_divides q w r) j.isLt) s.isLt⟩))
      ⟨effectiveIndex (2^q) (UniformResidualFibers.inverseOrientation v inverse) j.val%2^q,Nat.mod_lt _ (Nat.two_pow_pos _)⟩=
    (signedMatrix q w r v hv inverse).mulVec X (DFTModelResidualBasisGeometry.permutation q w r v p hp j) := by
  obtain ⟨⟨b,t⟩,rfl⟩:=(flat q w r).surjective j
  rw [show DFTModelResidualBasisGeometry.permutation q w r v p hp (flat q w r (b,t))=
    fibers q w r v p hp (b,t) from fibers_flat q w r v p hp b t,signed_fibers]
  let t' : Fin (2^q) := if UniformResidualFibers.inverseOrientation v inverse then
    xorIndex t (UniformPhysicalBinaryInverse.mask q) else t
  have ind:=index_flat q w r (UniformResidualFibers.inverseOrientation v inverse) b t
  change effectiveIndex (2^q) (UniformResidualFibers.inverseOrientation v inverse) (flat q w r (b,t)).val=b.val*2^q+t'.val at ind
  have div : effectiveIndex (2^q) (UniformResidualFibers.inverseOrientation v inverse) (flat q w r (b,t)).val/2^q=b.val := by
    rw [ind,Nat.add_comm,Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt t'.isLt,Nat.zero_add]
  have mod : effectiveIndex (2^q) (UniformResidualFibers.inverseOrientation v inverse) (flat q w r (b,t)).val%2^q=t'.val := by
    simp only [ind,Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_eq_of_lt t'.isLt]
  simp only [div,mod]
  congr 1
  funext s
  apply congrArg X
  rw [←fibers_flat q w r v p hp b s]
  congr 1
  apply Fin.ext
  exact (flat_value q w r b s).symm

end
end ExactFourierCircuits.DFTModelSavingResidualNative

import UniformNativeCopiedInverse
set_option autoImplicit false
namespace ExactFourierCircuits.UniformNativeResidualSemantics
open OAI.ExactFourier BinaryFrames DirectionalWords UniformResidualFibers
open UniformResidualNativeCoordinates UniformBinaryXorCoordinates
open UniformBinaryTensorCoordinates UniformNativeCopiedInverse
open scoped BigOperators
noncomputable section

/-- Cancels the signed-word compiler's static enumeration. Runtime addresses
are the explicit little-endian integers defined by binaryCoordinates. -/
def originalToNative (k : ℕ) : Fin (2^k) ≃ Fin (2^k) :=
 (addresses k).symm.trans (binaryCoordinates k).symm

def nativeWordMatrix {k : ℕ} (T : List (WordStep C (2^k))) :=
 Matrix.reindex (originalToNative k) (originalToNative k) (wordMatrix T)

/-- An original residual's geometric orientation and weight-three phase
select precisely a physical positive copied kernel or its inverse. -/
theorem native_signed_columns (q w : ℕ) (v : Bits (w+1)) (hv : dot v v=1)
 (p : Fin (w+1)) (hp : v p=1) (decreasing : Bool) :
 nativeWordMatrix (signedColumnWord q v hv decreasing)=
 if inverseOrientation v decreasing then (nativeCopiedMatrix q w v)⁻¹
 else nativeCopiedMatrix q w v := by
 unfold nativeWordMatrix
 rw [signedColumnWord_matrix q v hv p hp]
 cases orient : inverseOrientation v decreasing
 · simp only [Bool.false_eq_true,ite_false]
   ext x y
   simp [originalToNative,nativeCopiedMatrix,Matrix.reindex_apply]
 · simp only [ite_true]
   rw [copiedInverseProduct_eq q v p hp,←copiedProduct_inverse q v p hp]
   rw [nativeCopiedMatrix,Matrix.inv_reindex]
   ext x y
   simp [originalToNative,Matrix.reindex_apply]

lemma spectator_array (k r : ℕ) (A : Matrix (Fin (2^k)) (Fin (2^k)) ℂ)
 (X : Fin (2^(k+r))→ℂ) (s : Fin (2^r)) (z : Fin (2^k)) :
 (spectatorMatrix k r A).mulVec X ((spectatorSplit k r).symm (s,z))=
 A.mulVec (fun y => X ((spectatorSplit k r).symm (s,y))) z := by
 unfold spectatorMatrix Matrix.mulVec dotProduct
 rw [←(spectatorSplit k r).symm.sum_comp,Fintype.sum_prod_type]
 simp [Matrix.reindex_apply,Matrix.one_apply]

/-- The algebra needed by the actual group handler: one SAME-q forward tensor
on each physical fiber, followed only in inverse orientation by selected-bit XOR.
High remainder bits stay fixed in both branches. -/
theorem native_signed_spectator_array (q w r : ℕ) (v : Bits (w+1))
 (hv : dot v v=1) (p : Fin (w+1)) (hp : v p=1) (decreasing : Bool)
 (X : Fin (2^(q*(w+1)+r))→ℂ) (s : Fin (2^r)) (b : Fin (2^(q*w))) (t : Fin (2^q)) :
 (spectatorMatrix (q*(w+1)) r
   (nativeWordMatrix (signedColumnWord q v hv decreasing))).mulVec X
 ((spectatorSplit (q*(w+1)) r).symm (s,nativeFiber q w v p hp (b,t)))=
 (physicalMatrix q).mulVec
   (fun z => X ((spectatorSplit (q*(w+1)) r).symm (s,nativeFiber q w v p hp (b,z))))
   (if inverseOrientation v decreasing then xorIndex t (UniformPhysicalBinaryInverse.mask q) else t) := by
 rw [native_signed_columns q w v hv p hp decreasing]
 cases orient : inverseOrientation v decreasing
 · simp only [Bool.false_eq_true,ite_false]
   rw [spectator_array,nativeCopied_array q w v p hp]
 · simp only [ite_true]
   rw [←spectator_inverse]
   exact copied_spectator_inverse_forward_xor q w r v p hp X s b t

end
end ExactFourierCircuits.UniformNativeResidualSemantics

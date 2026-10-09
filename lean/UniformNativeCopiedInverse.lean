import UniformResidualNativeCoordinates
import UniformPhysicalBinaryInverse
set_option autoImplicit false
namespace ExactFourierCircuits.UniformNativeCopiedInverse
open OAI.ExactFourier DirectionalWords BinaryFrames UniformResidualNativeCoordinates UniformBinaryTensorCoordinates UniformBinaryXorCoordinates
open UniformPhysicalBinaryInverse (mask)
open scoped BigOperators Kronecker
noncomputable section

lemma native_inverse_blocks(q w:ℕ)(v:Bits (w+1))(p:Fin (w+1))(hp:v p=1):
 (nativeCopiedMatrix q w v)⁻¹=Matrix.reindex (nativeFiber q w v p hp) (nativeFiber q w v p hp)
 ((1:Matrix (Fin (2^(q*w))) (Fin (2^(q*w))) ℂ)⊗ₖ(physicalMatrix q)⁻¹):=by
 rw [nativeCopied_blocks q w v p hp,Matrix.inv_reindex,Matrix.inv_kronecker,inv_one]

theorem native_inverse_array(q w:ℕ)(v:Bits (w+1))(p:Fin (w+1))(hp:v p=1)
 (X:Fin (2^(q*(w+1)))→ℂ)(b:Fin (2^(q*w)))(t:Fin (2^q)):
 ((nativeCopiedMatrix q w v)⁻¹).mulVec X (nativeFiber q w v p hp (b,t))=
 ((physicalMatrix q)⁻¹).mulVec (fun s=>X (nativeFiber q w v p hp (b,s))) t:=by
 rw [native_inverse_blocks q w v p hp]
 unfold Matrix.mulVec dotProduct
 rw [←(nativeFiber q w v p hp).sum_comp,Fintype.sum_prod_type]
 simp [Matrix.reindex_apply,Matrix.one_apply]

theorem native_inverse_forward_xor(q w:ℕ)(v:Bits (w+1))(p:Fin (w+1))(hp:v p=1)
 (X:Fin (2^(q*(w+1)))→ℂ)(b:Fin (2^(q*w)))(t:Fin (2^q)):
 ((nativeCopiedMatrix q w v)⁻¹).mulVec X (nativeFiber q w v p hp (b,t))=
 (physicalMatrix q).mulVec (fun s=>X (nativeFiber q w v p hp (b,s))) (xorIndex t (mask q)):=by
 rw [native_inverse_array,UniformPhysicalBinaryInverse.inverse_mulVec]

/-- High remainder bits remain spectators in this explicit numeric product. -/
def spectatorSplit(k r:ℕ):Fin (2^(k+r))≃Fin (2^r)×Fin (2^k):=
 (finCongr (by rw [Nat.pow_add];ring)).trans finProdFinEquiv.symm
def spectatorMatrix(k r:ℕ)(A:Matrix (Fin (2^k)) (Fin (2^k)) ℂ):Matrix (Fin (2^(k+r))) (Fin (2^(k+r))) ℂ:=
 Matrix.reindex (spectatorSplit k r).symm (spectatorSplit k r).symm
 ((1:Matrix (Fin (2^r)) (Fin (2^r)) ℂ)⊗ₖA)
lemma spectator_inverse(k r:ℕ)(A:Matrix (Fin (2^k)) (Fin (2^k)) ℂ):
 (spectatorMatrix k r A)⁻¹=spectatorMatrix k r A⁻¹:=by
 rw [spectatorMatrix,Matrix.inv_reindex,Matrix.inv_kronecker,inv_one];rfl
lemma spectator_inverse_array(k r:ℕ)(A:Matrix (Fin (2^k)) (Fin (2^k)) ℂ)
 (X:Fin (2^(k+r))→ℂ)(s:Fin (2^r))(z:Fin (2^k)):
 ((spectatorMatrix k r A)⁻¹).mulVec X ((spectatorSplit k r).symm (s,z))=
 A⁻¹.mulVec (fun y=>X ((spectatorSplit k r).symm (s,y))) z:=by
 rw [spectator_inverse]
 unfold spectatorMatrix Matrix.mulVec dotProduct
 rw [←(spectatorSplit k r).symm.sum_comp,Fintype.sum_prod_type]
 simp [Matrix.reindex_apply,Matrix.one_apply]

/-- Exact inverse copied residual with all spectators. Only the selected
innermost q coordinates are flipped after the single positive child action. -/
theorem copied_spectator_inverse_forward_xor(q w r:ℕ)(v:Bits (w+1))(p:Fin (w+1))(hp:v p=1)
 (X:Fin (2^(q*(w+1)+r))→ℂ)(s:Fin (2^r))(b:Fin (2^(q*w)))(t:Fin (2^q)):
 ((spectatorMatrix (q*(w+1)) r (nativeCopiedMatrix q w v))⁻¹).mulVec X
 ((spectatorSplit (q*(w+1)) r).symm (s,nativeFiber q w v p hp (b,t)))=
 (physicalMatrix q).mulVec
 (fun z=>X ((spectatorSplit (q*(w+1)) r).symm (s,nativeFiber q w v p hp (b,z))))
 (xorIndex t (mask q)):=by
 rw [spectator_inverse_array,native_inverse_forward_xor]
end
end ExactFourierCircuits.UniformNativeCopiedInverse

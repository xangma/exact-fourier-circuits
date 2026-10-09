import UniformNativeScheduleMatrix
import UniformNativeResidualSemantics
set_option autoImplicit false
namespace ExactFourierCircuits.UniformNativeRoleSemantics
open OAI.ExactFourier UniformBinaryTensorCoordinates UniformNativeCopiedInverse
open UniformNativeScheduleMatrix UniformNativeResidualSemantics
open scoped BigOperators
noncomputable section

lemma bit_same : TensorWords.bitEquiv=UniformBinaryXorCoordinates.bitEquiv := by
 ext i
 fin_cases i <;> rfl

/-- Physical role-major relabel from the original signed frame's addresses. -/
def originalCoordinates (R k : ℕ) : Fin (R*2^k) ≃ Fin (R*2^k) :=
 (RoleWords.roleAddresses R k).symm.trans
  (((Equiv.refl (Fin R)).prodCongr (originalToNative k)).trans
   (RoleWords.roleAddresses R k))

lemma coordinate_cancellation (k : ℕ) :
 (TensorWords.tensorRelabel k).trans (toAbstract k).symm=originalToNative k := by
 apply Equiv.ext
 intro z
 apply (UniformBinaryXorCoordinates.binaryCoordinates k).injective
 have same : TensorWords.tensorBits k=
  Equiv.piCongrRight (fun _ : Fin k => UniformBinaryXorCoordinates.bitEquiv) := by
  unfold TensorWords.tensorBits
  rw [bit_same]
 simp [TensorWords.tensorRelabel,toAbstract,originalToNative,
  UniformBinaryXorCoordinates.binaryCoordinates,same]


/-- Cancels both static address relabels before interpreting a real role word. -/
theorem native_canonical_matrix (R k : ℕ) (T : List (WordStep C (R*2^k))) :
 nativeMatrix R k (wordMatrix (PaddingWords.canonicalNetworkWord R k T))=
 Matrix.reindex (originalCoordinates R k) (originalCoordinates R k) (wordMatrix T) := by
 unfold PaddingWords.canonicalNetworkWord nativeMatrix
 rw [TypedKernelWords.relabelWord_matrix]
 have eq : (PaddingWords.addressRelabel R k).trans (nativeCoordinates R k)=originalCoordinates R k := by
  apply Equiv.ext
  intro z
  obtain ⟨⟨i,z⟩,rfl⟩ := (RoleWords.roleAddresses R k).surjective z
  simpa [PaddingWords.addressRelabel,nativeCoordinates,originalCoordinates] using
   congrArg (fun a => RoleWords.roleAddresses R k (i,a)) (Equiv.congr_fun (coordinate_cancellation k) z)
 ext x y
 change wordMatrix T (((PaddingWords.addressRelabel R k).trans (nativeCoordinates R k)).symm x)
  (((PaddingWords.addressRelabel R k).trans (nativeCoordinates R k)).symm y)=_
 rw [eq]
 rfl

lemma originalCoordinates_role (R k : ℕ) (i : Fin R) (z : Fin (2^k)) :
 originalCoordinates R k (RoleWords.roleAddresses R k (i,z))=
 RoleWords.roleAddresses R k (i,originalToNative k z) := by simp [originalCoordinates]

/-- The original residual matrix acts on exactly its actual numerical role;
all other arbitrary role arrays are fixed. -/
theorem native_canonical_role (R k : ℕ) (i : Fin R)
 (T : List (WordStep C (2^k))) :
 nativeMatrix R k (wordMatrix (PaddingWords.canonicalNetworkWord R k (RoleFrameWords.roleWord i T)))=
 Embedded.matrix (RoleFrameWords.roleEmbedding i) (nativeWordMatrix T) := by
 rw [native_canonical_matrix,RoleFrameWords.roleWord_matrix]
 unfold nativeWordMatrix
 rw [←Embedded.matrix_equiv (originalCoordinates R k),
  ←Embedded.matrix_equiv (originalToNative k),Embedded.matrix_comp,Embedded.matrix_comp]
 apply congrArg (fun e : Fin (2^k)↪Fin (R*2^k) => Embedded.matrix e (wordMatrix T))
 apply Function.Embedding.ext
 intro z
 simp [originalCoordinates,RoleFrameWords.roleEmbedding_apply]

end
end ExactFourierCircuits.UniformNativeRoleSemantics

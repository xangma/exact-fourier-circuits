import UniformRecursivePaddingExecution
import UniformNativeRecordRoles
import UniformNativeScheduleSemantics
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursivePaddingSemantic
open OAI.ExactFourier UniformNativeScheduleMatrix UniformNativeRecordRoles
open UniformNativeCopiedInverse UniformNativeResidualSemantics UniformBinaryTensorCoordinates
open scoped BigOperators
noncomputable section

def tailRole (w p : ℕ) (hw : w ≤ 2^p) : Fin (2^p-w) ↪ Fin (2^p) :=
 Function.Embedding.inr.trans (PaddingWords.paddingRoles w p hw).toEmbedding
def tailAddress (w p k : ℕ) (hw : w ≤ 2^p) : Fin ((2^p-w)*2^k) ↪ Fin (2^p*2^k) :=
 Function.Embedding.inr.trans
  (PaddingWords.blockCoordinates k (PaddingWords.paddingRoles w p hw)).toEmbedding
lemma tailAddress_role (w p k : ℕ) (hw : w ≤ 2^p) :
 tailAddress w p k hw=TripleSchedule.Global.addressEmbedding (n:=k) (tailRole w p hw) := by
 apply Function.Embedding.ext
 intro z
 obtain ⟨⟨i,z⟩,rfl⟩ := (RoleWords.roleAddresses (2^p-w) k).surjective z
 simp [tailAddress,PaddingWords.blockCoordinates,tailRole,TripleSchedule.Global.addressEmbedding]

lemma tail_native (w p k : ℕ) (hw : w ≤ 2^p) :
 nativeMatrix (2^p) k (wordMatrix (TensorWords.embeddedWord (tailAddress w p k hw)
  (PaddingWords.ordinaryCopiesWord (2^p-w) k)))=
 Embedded.matrix (tailAddress w p k hw)
  (PaddingWords.copiesMatrix (2^p-w) k (physicalMatrix k)) := by
 rw [TensorWords.embeddedWord_matrix,PaddingWords.ordinaryCopiesWord_matrix,
  tailAddress_role,native_embedding,native_copies]

lemma tail_array {w a R : ℕ} (k : ℕ) (e : Fin w ⊕ Fin a ≃ Fin R)
 (M : Matrix (Fin (2^k)) (Fin (2^k)) ℂ)
 (X : Fin R→Fin (2^k)→ℂ) (i : Fin w ⊕ Fin a) (z : Fin (2^k)) :
 (Embedded.matrix (Function.Embedding.inr.trans (PaddingWords.blockCoordinates k e).toEmbedding)
  (PaddingWords.copiesMatrix a k M)).mulVec (RoleWords.arrayValues k X)
  (RoleWords.roleAddresses R k (e i,z))=
 match i with
 | .inl j => X (e (.inl j)) z
 | .inr j => M.mulVec (X (e (.inr j))) z := by
 rw [←Embedded.matrix_comp,Embedded.matrix_equiv,Embedded.matrix_inr]
 cases i with
 | inl i =>
  have coords : RoleWords.roleAddresses R k (e (.inl i),z)=
   PaddingWords.blockCoordinates k e (.inl (RoleWords.roleAddresses w k (i,z))) := by
   simp [PaddingWords.blockCoordinates]
  rw [coords,reindex_mulVec]
  simp [Matrix.fromBlocks_mulVec,PaddingWords.blockCoordinates]
 | inr i =>
  have coords : RoleWords.roleAddresses R k (e (.inr i),z)=
   PaddingWords.blockCoordinates k e (.inr (RoleWords.roleAddresses a k (i,z))) := by
   simp [PaddingWords.blockCoordinates]
  rw [coords,reindex_mulVec]
  simp only [Function.comp_apply,Equiv.symm_apply_apply,Matrix.fromBlocks_mulVec,Sum.elim_inr,
   Matrix.zero_mulVec,zero_add]
  have data : (fun x => RoleWords.arrayValues k X (PaddingWords.blockCoordinates k e (.inr x)))=
   RoleWords.arrayValues k (fun j y => X (e (.inr j)) y) := by
   funext x
   obtain ⟨⟨j,y⟩,rfl⟩ := (RoleWords.roleAddresses a k).surjective x
   simp [PaddingWords.blockCoordinates]
  change (PaddingWords.copiesMatrix a k M).mulVec
   (fun x => RoleWords.arrayValues k X (PaddingWords.blockCoordinates k e (.inr x)))
   (RoleWords.roleAddresses a k (i,z))=_
  rw [data,copies_array]

lemma tail_array_threshold (w p k : ℕ) (hw : w ≤ 2^p)
 (M : Matrix (Fin (2^k)) (Fin (2^k)) ℂ)
 (X : Fin (2^p)→Fin (2^k)→ℂ) (i : Fin (2^p)) (z : Fin (2^k)) :
 (Embedded.matrix (tailAddress w p k hw) (PaddingWords.copiesMatrix (2^p-w) k M)).mulVec
  (RoleWords.arrayValues k X) (RoleWords.roleAddresses (2^p) k (i,z))=
 if w ≤ i.val then M.mulVec (X i) z else X i z := by
 obtain ⟨i,rfl⟩ := (PaddingWords.paddingRoles w p hw).surjective i
 rw [tailAddress,tail_array]
 cases i with
 | inl i => simp [PaddingWords.paddingRoles,not_le_of_gt i.isLt]
 | inr i => simp [PaddingWords.paddingRoles]

lemma tail_spectator_array (w p k r : ℕ) (hw : w ≤ 2^p)
 (M : Matrix (Fin (2^k)) (Fin (2^k)) ℂ)
 (X : Fin (2^p)→Fin (2^(k+r))→ℂ) (i : Fin (2^p)) (z : Fin (2^(k+r))) :
 (spectatorLift (2^p) k r
  (Embedded.matrix (tailAddress w p k hw) (PaddingWords.copiesMatrix (2^p-w) k M))).mulVec
  (RoleWords.arrayValues (k+r) X) (RoleWords.roleAddresses (2^p) (k+r) (i,z))=
 if w ≤ i.val then (spectatorMatrix k r M).mulVec (X i) z else X i z := by
 obtain ⟨⟨s,z⟩,rfl⟩ := (spectatorSplit k r).symm.surjective z
 rw [←spectatorCoordinates_at,spectatorLift_array]
 have data :
  (fun y => RoleWords.arrayValues (k+r) X (spectatorCoordinates (2^p) k r (s,y)))=
  RoleWords.arrayValues k (fun i y => X i ((spectatorSplit k r).symm (s,y))) := by
  funext y
  obtain ⟨⟨a,y⟩,rfl⟩ := (RoleWords.roleAddresses (2^p) k).surjective y
  rw [spectatorCoordinates_at,RoleWords.arrayValues_at,RoleWords.arrayValues_at]
 rw [data,tail_array_threshold,spectator_array]

theorem padding_array (q r : ℕ)
 (X : Fin UniformFixedNetwork.W→Fin (2^(q*UniformFixedNetwork.m+r))→ℂ)
 (i : Fin UniformFixedNetwork.W) (z : Fin (2^(q*UniformFixedNetwork.m+r))) :
 (UniformNativeScheduleSemantics.semantic q r .padding).mulVec
  (RoleWords.arrayValues (q*UniformFixedNetwork.m+r) X)
  (RoleWords.roleAddresses UniformFixedNetwork.W (q*UniformFixedNetwork.m+r) (i,z))=
 if TripleSchedule.Global.size ExplicitSeedBudget.h ≤ i.val then
  (spectatorMatrix (q*UniformFixedNetwork.m) r (physicalMatrix (q*UniformFixedNetwork.m))).mulVec (X i) z
 else X i z := by
 change (spectatorLift (2^ExplicitSeedBudget.roleBits) (q*UniformFixedNetwork.m) r
  (nativeMatrix (2^ExplicitSeedBudget.roleBits) (q*UniformFixedNetwork.m)
   (wordMatrix (TensorWords.embeddedWord
    (tailAddress (TripleSchedule.Global.size ExplicitSeedBudget.h) ExplicitSeedBudget.roleBits
     (q*UniformFixedNetwork.m) MasterBudget.seed_actual_padding)
    (PaddingWords.ordinaryCopiesWord (2^ExplicitSeedBudget.roleBits-TripleSchedule.Global.size ExplicitSeedBudget.h)
     (q*UniformFixedNetwork.m)))))).mulVec _ _=_
 rw [tail_native]
 exact tail_spectator_array _ _ _ _ MasterBudget.seed_actual_padding _ X i z

/-- The pointwise output of the real remaining-role loop is exactly the typed
padding instruction on the flattened, otherwise arbitrary, full role array. -/
theorem padding_values (q r : ℕ)
 (X Y : Fin UniformFixedNetwork.W→Fin (2^(q*UniformFixedNetwork.m+r))→ℂ)
 (output : ∀i, Y i = if TripleSchedule.Global.size ExplicitSeedBudget.h ≤ i.val then
  (spectatorMatrix (q*UniformFixedNetwork.m) r (physicalMatrix (q*UniformFixedNetwork.m))).mulVec (X i)
  else X i) :
 RoleWords.arrayValues (q*UniformFixedNetwork.m+r) Y=
 (UniformNativeScheduleSemantics.semantic q r .padding).mulVec
  (RoleWords.arrayValues (q*UniformFixedNetwork.m+r) X) := by
 funext z
 obtain ⟨⟨i,z⟩,rfl⟩ := (RoleWords.roleAddresses UniformFixedNetwork.W
  (q*UniformFixedNetwork.m+r)).surjective z
 rw [RoleWords.arrayValues_at,padding_array,output]
 split <;> rfl

end
end ExactFourierCircuits.UniformRecursivePaddingSemantic

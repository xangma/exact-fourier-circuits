import UniformNativeRoleSemantics
set_option autoImplicit false
namespace ExactFourierCircuits.UniformNativeRecordRoles
open OAI.ExactFourier UniformBinaryTensorCoordinates UniformNativeCopiedInverse
open UniformNativeScheduleMatrix UniformNativeResidualSemantics UniformNativeRoleSemantics
open scoped BigOperators
noncomputable section

lemma lifted_role_matrix {r R k : ℕ} (e : Fin r↪Fin R) (i : Fin r)
 (T : List (WordStep C (2^k))) :
 wordMatrix (TripleSchedule.Global.liftWord e (RoleFrameWords.roleWord i T))=
 wordMatrix (RoleFrameWords.roleWord (e i) T) := by
 rw [TripleSchedule.Global.liftWord,TensorWords.embeddedWord_matrix,
  RoleFrameWords.roleWord_matrix,RoleFrameWords.roleWord_matrix,Embedded.matrix_comp]
 apply congrArg (fun f : Fin (2^k)↪Fin (R*2^k) => Embedded.matrix f (wordMatrix T))
 apply Function.Embedding.ext
 intro z
 simp [RoleFrameWords.roleEmbedding_apply]

/-- Lifting a local invocation uses the actual global destination role. -/
theorem native_lifted_role {r R k : ℕ} (e : Fin r↪Fin R) (i : Fin r)
 (T : List (WordStep C (2^k))) :
 nativeMatrix R k (wordMatrix (PaddingWords.canonicalNetworkWord R k
  (TripleSchedule.Global.liftWord e (RoleFrameWords.roleWord i T))))=
 Embedded.matrix (RoleFrameWords.roleEmbedding (e i)) (nativeWordMatrix T) := by
 rw [native_canonical_matrix,lifted_role_matrix,←native_canonical_matrix,native_canonical_role]

/-- Role embeddings commute with the physical address relabel. -/
lemma native_embedding {r R k : ℕ} (e : Fin r↪Fin R)
 (M : Matrix (Fin (r*2^k)) (Fin (r*2^k)) ℂ) :
 nativeMatrix R k (Embedded.matrix (TripleSchedule.Global.addressEmbedding (n:=k) e) M)=
 Embedded.matrix (TripleSchedule.Global.addressEmbedding (n:=k) e) (nativeMatrix r k M) := by
 unfold nativeMatrix
 rw [←Embedded.matrix_equiv (nativeCoordinates R k),
  ←Embedded.matrix_equiv (nativeCoordinates r k),Embedded.matrix_comp,Embedded.matrix_comp]
 apply congrArg (fun f : Fin (r*2^k)↪Fin (R*2^k) => Embedded.matrix f M)
 apply Function.Embedding.ext
 intro z
 obtain ⟨⟨i,z⟩,rfl⟩ := (RoleWords.roleAddresses r k).surjective z
 simp [nativeCoordinates]

lemma embedding_role {r R k : ℕ} (e : Fin r↪Fin R) (i : Fin r)
 (M : Matrix (Fin (2^k)) (Fin (2^k)) ℂ) :
 Embedded.matrix (TripleSchedule.Global.addressEmbedding (n:=k) e)
  (Embedded.matrix (RoleFrameWords.roleEmbedding i) M)=
 Embedded.matrix (RoleFrameWords.roleEmbedding (e i)) M := by
 rw [Embedded.matrix_comp]
 apply congrArg (fun f : Fin (2^k)↪Fin (R*2^k) => Embedded.matrix f M)
 apply Function.Embedding.ext
 intro z
 simp [RoleFrameWords.roleEmbedding_apply]

def paddingRole (w p : ℕ) (hw : w≤2^p) : Fin w↪Fin (2^p) :=
 Function.Embedding.inl.trans (PaddingWords.paddingRoles w p hw).toEmbedding

def paddingAddress (w p k : ℕ) (hw : w≤2^p) : Fin (w*2^k)↪Fin (2^p*2^k) :=
 Function.Embedding.inl.trans (PaddingWords.blockCoordinates k (PaddingWords.paddingRoles w p hw)).toEmbedding

lemma paddingAddress_role (w p k : ℕ) (hw : w≤2^p) :
 paddingAddress w p k hw=TripleSchedule.Global.addressEmbedding (n:=k) (paddingRole w p hw) := by
 apply Function.Embedding.ext
 intro z
 obtain ⟨⟨i,z⟩,rfl⟩ := (RoleWords.roleAddresses w k).surjective z
 simp [paddingAddress,PaddingWords.blockCoordinates,paddingRole,
  TripleSchedule.Global.addressEmbedding]

/-- The padded active role has its original numerical destination value. -/
lemma paddingRole_value (w p : ℕ) (hw : w≤2^p) (i : Fin w) :
 (paddingRole w p hw i).val=i.val := by
 simp [paddingRole,PaddingWords.paddingRoles]

/-- Full role correspondence for a real residual macro: invocation embedding,
canonical address relabel, active-role padding, and physical address relabel. -/
theorem native_active_lifted_role {r w : ℕ} (p k : ℕ) (hw : w≤2^p)
 (e : Fin r↪Fin w) (i : Fin r) (T : List (WordStep C (2^k))) :
 nativeMatrix (2^p) k (wordMatrix (TensorWords.embeddedWord (paddingAddress w p k hw)
  (PaddingWords.canonicalNetworkWord w k
   (TripleSchedule.Global.liftWord e (RoleFrameWords.roleWord i T)))))=
 Embedded.matrix (RoleFrameWords.roleEmbedding (paddingRole w p hw (e i))) (nativeWordMatrix T) := by
 rw [TensorWords.embeddedWord_matrix,paddingAddress_role,native_embedding,
  native_lifted_role,embedding_role]

/-- An arbitrary high spectator slice receives this exact selected-role action,
with every other arbitrary role array unchanged. -/
theorem spectator_role_array (R k r : ℕ) (i j : Fin R)
 (M : Matrix (Fin (2^k)) (Fin (2^k)) ℂ)
 (X : Fin R→Fin (2^(k+r))→ℂ) (s : Fin (2^r)) (z : Fin (2^k)) :
 (spectatorLift R k r (Embedded.matrix (RoleFrameWords.roleEmbedding i) M)).mulVec
  (RoleWords.arrayValues (k+r) X)
  (RoleWords.roleAddresses R (k+r) (j,(spectatorSplit k r).symm (s,z)))=
 if j=i then M.mulVec (fun y => X i ((spectatorSplit k r).symm (s,y))) z
 else X j ((spectatorSplit k r).symm (s,z)) := by
 rw [←spectatorCoordinates_at,spectatorLift_array]
 have data :
  (fun y => RoleWords.arrayValues (k+r) X (spectatorCoordinates R k r (s,y)))=
  RoleWords.arrayValues k (fun i y => X i ((spectatorSplit k r).symm (s,y))) := by
  funext y
  obtain ⟨⟨a,y⟩,rfl⟩ := (RoleWords.roleAddresses R k).surjective y
  rw [spectatorCoordinates_at,RoleWords.arrayValues_at,RoleWords.arrayValues_at]
 rw [data]
 by_cases h : j=i
 · subst j
   simp only [ite_true]
   exact RoleFrameWords.roleMatrix_selected_apply _ _ _ _
 · simp only [h,ite_false]
   exact RoleFrameWords.roleMatrix_untouched_apply i j h _ _ _

end
end ExactFourierCircuits.UniformNativeRecordRoles

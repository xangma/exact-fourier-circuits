import UniformNativeRecordRoles
import UniformFixedNetworkShearChildMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformNativeScalarAlgebra
open OAI.ExactFourier UniformNativeScheduleMatrix UniformNativeRoleSemantics
open UniformNativeRecordRoles UniformNativeCopiedInverse UniformResidualNativeCoordinates
open scoped BigOperators
noncomputable section

lemma pointwise_at {R : ℕ} (k : ℕ) (M : Matrix (Fin R) (Fin R) ℂ)
 (i j : Fin R) (a b : Fin (2^k)) :
 RoleWords.pointwiseMatrix k M (RoleWords.roleAddresses R k (i,a))
  (RoleWords.roleAddresses R k (j,b))=M i j*(if a=b then 1 else 0) := by
 simp [RoleWords.pointwiseMatrix,Matrix.reindex_apply,Matrix.one_apply]

/-- Extension by identity commutes with pointwise role operations. -/
theorem pointwise_embedding {r R : ℕ} (k : ℕ) (e : Fin r↪Fin R)
 (M : Matrix (Fin r) (Fin r) ℂ) :
 Embedded.matrix (TripleSchedule.Global.addressEmbedding (n:=k) e)
  (RoleWords.pointwiseMatrix k M)=RoleWords.pointwiseMatrix k (Embedded.matrix e M) := by
 classical
 ext x y
 obtain ⟨⟨i,a⟩,rfl⟩:=(RoleWords.roleAddresses R k).surjective x
 obtain ⟨⟨j,b⟩,rfl⟩:=(RoleWords.roleAddresses R k).surjective y
 rw [pointwise_at]
 by_cases hi:i∈Set.range e
 · obtain ⟨i,rfl⟩:=hi
   by_cases hj:j∈Set.range e
   · obtain ⟨j,rfl⟩:=hj
     rw [←TripleSchedule.Global.addressEmbedding_at,←TripleSchedule.Global.addressEmbedding_at,
      Embedded.matrix_on,pointwise_at,Embedded.matrix_on]
   · rw [Embedded.matrix_off_col _ _ _ _
      (TripleSchedule.Global.addressEmbedding_not_mem e j hj b),Embedded.matrix_off_col e M _ _ hj]
     have ne:e i≠j:=fun h=>hj ⟨i,h⟩
     have addr:RoleWords.roleAddresses R k (e i,a)≠RoleWords.roleAddresses R k (j,b):=by
      intro h;exact ne (congrArg Prod.fst ((RoleWords.roleAddresses R k).injective h))
     simp [ne,addr]
 · rw [Embedded.matrix_off_row _ _ _ _
     (TripleSchedule.Global.addressEmbedding_not_mem e i hi a),Embedded.matrix_off_row e M _ _ hi]
   by_cases ij:i=j <;> by_cases ab:a=b <;>
    simp [ij,ab,(RoleWords.roleAddresses R k).injective.eq_iff,Prod.mk.injEq]

lemma pointwise_reindex (R k : ℕ) (f : Fin (2^k)≃Fin (2^k))
 (M : Matrix (Fin R) (Fin R) ℂ) :
 Matrix.reindex ((RoleWords.roleAddresses R k).symm.trans
  (((Equiv.refl (Fin R)).prodCongr f).trans (RoleWords.roleAddresses R k)))
  ((RoleWords.roleAddresses R k).symm.trans
  (((Equiv.refl (Fin R)).prodCongr f).trans (RoleWords.roleAddresses R k)))
  (RoleWords.pointwiseMatrix k M)=RoleWords.pointwiseMatrix k M := by
 ext x y
 obtain ⟨⟨i,a⟩,rfl⟩:=(RoleWords.roleAddresses R k).surjective x
 obtain ⟨⟨j,b⟩,rfl⟩:=(RoleWords.roleAddresses R k).surjective y
 simp [RoleWords.pointwiseMatrix,Matrix.reindex_apply,Matrix.one_apply]

theorem original_pointwise (R k : ℕ) (M : Matrix (Fin R) (Fin R) ℂ) :
 Matrix.reindex (originalCoordinates R k) (originalCoordinates R k)
  (RoleWords.pointwiseMatrix k M)=RoleWords.pointwiseMatrix k M :=
 pointwise_reindex R k (UniformNativeResidualSemantics.originalToNative k) M

theorem native_pointwise (R k : ℕ) (M : Matrix (Fin R) (Fin R) ℂ) :
 nativeMatrix R k (RoleWords.pointwiseMatrix k M)=RoleWords.pointwiseMatrix k M := by
 unfold nativeMatrix nativeCoordinates
 exact pointwise_reindex R k (UniformBinaryTensorCoordinates.toAbstract k).symm M

theorem embedded_shear {r R : ℕ} (e : Fin r↪Fin R) (d s : Fin r) (ne:d≠s) (t : ℂ) :
 Embedded.matrix e (1+Matrix.single d s t)=1+Matrix.single (e d) (e s) t := by
 have ene:e d≠e s:=fun h=>ne (e.injective h)
 have pairs:(Embedded.pair d s ne).trans e=Embedded.pair (e d) (e s) ene := by
  apply Function.Embedding.ext
  intro i
  fin_cases i <;> rfl
 have h:=congrArg (Embedded.matrix e) (Embedded.pair_matrix d s ne t (0:ℂ))
 rw [Embedded.matrix_comp,pairs,Embedded.pair_matrix] at h
 simpa using h.symm

/-- Literal invocation, canonical relabel and active-role padding produce the
 exact physical scalar matrix, without imposing an array invariant. -/
theorem native_active_shear {r R : ℕ} (p k : ℕ) (hw:R ≤ 2^p)
 (e : Fin r↪Fin R) (d s : Fin r) (ne:d≠s) (t : ℂ) (ht:t≠0) :
 nativeMatrix (2^p) k (wordMatrix (TensorWords.embeddedWord (paddingAddress R p k hw)
  (PaddingWords.canonicalNetworkWord R k (TripleSchedule.Global.liftWord e
   (RoleWords.pointwiseShearWord k d s ne t ht)))))=
 RoleWords.pointwiseMatrix k (1+Matrix.single (paddingRole R p hw (e d))
  (paddingRole R p hw (e s)) t) := by
 rw [TensorWords.embeddedWord_matrix,paddingAddress_role,native_embedding,native_canonical_matrix,
  TripleSchedule.Global.liftWord,TensorWords.embeddedWord_matrix,RoleWords.pointwiseShearWord_matrix,
  pointwise_embedding,original_pointwise,pointwise_embedding,Embedded.matrix_comp,
  embedded_shear (e.trans (paddingRole R p hw)) d s ne t]
 rfl

lemma spectator_pointwise_array (R k rest : ℕ) (M : Matrix (Fin R) (Fin R) ℂ)
 (X : Fin R→Fin (2^(k+rest))→ℂ) (i : Fin R) (s : Fin (2^rest)) (z : Fin (2^k)) :
 (spectatorLift R k rest (RoleWords.pointwiseMatrix k M)).mulVec
  (RoleWords.arrayValues (k+rest) X)
  (RoleWords.roleAddresses R (k+rest) (i,(spectatorSplit k rest).symm (s,z)))=
 M.mulVec (fun j=>X j ((spectatorSplit k rest).symm (s,z))) i := by
 rw [←spectatorCoordinates_at,spectatorLift_array]
 have data:(fun y=>RoleWords.arrayValues (k+rest) X (spectatorCoordinates R k rest (s,y)))=
  RoleWords.arrayValues k (fun j a=>X j ((spectatorSplit k rest).symm (s,a))) := by
  funext y
  obtain ⟨⟨j,a⟩,rfl⟩:=(RoleWords.roleAddresses R k).surjective y
  rw [spectatorCoordinates_at,RoleWords.arrayValues_at,RoleWords.arrayValues_at]
 rw [data,RoleWords.pointwiseMatrix_apply]

theorem spectator_shear_values (R k rest : ℕ) (d s : Fin R) (t : ℂ)
 (f : Fin R→Fin (2^(k+rest))→UniformMachine.Scalar) :
 (spectatorLift R k rest (RoleWords.pointwiseMatrix k (1+Matrix.single d s t))).mulVec
  (RoleWords.arrayValues (k+rest) (fun i a=>(f i a).value))=
 RoleWords.arrayValues (k+rest) (fun i a=>(UniformFixedNetworkShearChildMachine.shearValues d s t f i a).value) := by
 funext x
 obtain ⟨⟨i,a⟩,rfl⟩:=(RoleWords.roleAddresses R (k+rest)).surjective x
 obtain ⟨⟨j,z⟩,rfl⟩:=(spectatorSplit k rest).symm.surjective a
 rw [spectator_pointwise_array,RoleWords.arrayValues_at,Matrix.add_mulVec,Matrix.one_mulVec]
 by_cases eq:i=d
 · subst i
   simp [Matrix.single_mulVec,UniformFixedNetworkShearChildMachine.shearValues,
    UniformFixedNetworkShearChildMachine.value,UniformInPlaceMachine.result,UniformInPlaceMachine.prepared]
 · simp [Matrix.single_mulVec,UniformFixedNetworkShearChildMachine.shearValues,eq]

theorem native_active_shear_values {r R : ℕ} (p k rest : ℕ) (hw:R ≤ 2^p)
 (e : Fin r↪Fin R) (d s : Fin r) (ne:d≠s) (t : ℂ) (ht:t≠0)
 (f : Fin (2^p)→Fin (2^(k+rest))→UniformMachine.Scalar) :
 (spectatorLift (2^p) k rest (nativeMatrix (2^p) k
  (wordMatrix (TensorWords.embeddedWord (paddingAddress R p k hw)
   (PaddingWords.canonicalNetworkWord R k (TripleSchedule.Global.liftWord e
    (RoleWords.pointwiseShearWord k d s ne t ht))))))).mulVec
  (RoleWords.arrayValues (k+rest) (fun i a=>(f i a).value))=
 RoleWords.arrayValues (k+rest) (fun i a=>(UniformFixedNetworkShearChildMachine.shearValues
  (paddingRole R p hw (e d)) (paddingRole R p hw (e s)) t f i a).value) := by
 rw [native_active_shear]
 exact spectator_shear_values (2^p) k rest _ _ t f

end
end ExactFourierCircuits.UniformNativeScalarAlgebra

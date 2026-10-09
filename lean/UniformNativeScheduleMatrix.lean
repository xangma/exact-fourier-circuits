import UniformFixedNetworkScheduleMachine
import UniformNativeCopiedInverse
set_option autoImplicit false
namespace ExactFourierCircuits.UniformNativeScheduleMatrix
open OAI.ExactFourier UniformBinaryTensorCoordinates UniformNativeCopiedInverse
open scoped BigOperators Kronecker
noncomputable section
def nativeCoordinates (R k : ℕ) : Fin (R*2^k) ≃ Fin (R*2^k) :=
 (RoleWords.roleAddresses R k).symm.trans
  (((Equiv.refl (Fin R)).prodCongr (toAbstract k).symm).trans
    (RoleWords.roleAddresses R k))

def nativeMatrix (R k : ℕ) (M : Matrix (Fin (R*2^k)) (Fin (R*2^k)) ℂ) :=
 Matrix.reindex (nativeCoordinates R k) (nativeCoordinates R k) M

lemma nativeMatrix_one (R k : ℕ) :
 nativeMatrix R k (1 : Matrix (Fin (R*2^k)) (Fin (R*2^k)) ℂ)=1 :=
 (Matrix.reindexAlgEquiv ℂ ℂ (nativeCoordinates R k)).map_one
lemma nativeMatrix_mul (R k : ℕ) (M N : Matrix (Fin (R*2^k)) (Fin (R*2^k)) ℂ) :
 nativeMatrix R k (M*N)=nativeMatrix R k M*nativeMatrix R k N :=
 (Matrix.reindexAlgEquiv ℂ ℂ (nativeCoordinates R k)).map_mul M N

lemma native_copies (R k : ℕ) :
 nativeMatrix R k (PaddingWords.copiesMatrix R k (tensorPower C k))=
 PaddingWords.copiesMatrix R k (physicalMatrix k) := by
 ext x y
 obtain ⟨⟨i,x⟩,rfl⟩ := (RoleWords.roleAddresses R k).surjective x
 obtain ⟨⟨j,y⟩,rfl⟩ := (RoleWords.roleAddresses R k).surjective y
 have bridge := congrFun (congrFun (abstract_bridge k) x) y
 simpa [nativeMatrix,nativeCoordinates,PaddingWords.copiesMatrix,
  Matrix.reindex_apply,Matrix.one_apply,Matrix.kroneckerMap_apply] using
  congrArg (fun z : ℂ => (if i=j then 1 else 0)*z) bridge

/-- Spectator is the high address coordinate; it never becomes an extra role. -/
def spectatorCoordinates (R k r : ℕ) :
 (Fin (2^r) × Fin (R*2^k)) ≃ Fin (R*2^(k+r)) :=
 (((Equiv.refl _).prodCongr (RoleWords.roleAddresses R k).symm).trans
   ((Equiv.prodAssoc _ _ _).symm.trans
     (((Equiv.prodComm _ _).prodCongr (Equiv.refl _)).trans
       ((Equiv.prodAssoc _ _ _).trans
         (((Equiv.refl _).prodCongr (spectatorSplit k r).symm).trans
           (RoleWords.roleAddresses R (k+r)))))))

lemma spectatorCoordinates_at (R k r : ℕ) (s : Fin (2^r))
 (i : Fin R) (z : Fin (2^k)) :
 spectatorCoordinates R k r (s,RoleWords.roleAddresses R k (i,z))=
 RoleWords.roleAddresses R (k+r) (i,(spectatorSplit k r).symm (s,z)) := by
 simp [spectatorCoordinates]

def spectatorLift (R k r : ℕ) (M : Matrix (Fin (R*2^k)) (Fin (R*2^k)) ℂ) :=
 Matrix.reindex (spectatorCoordinates R k r) (spectatorCoordinates R k r)
  ((1 : Matrix (Fin (2^r)) (Fin (2^r)) ℂ) ⊗ₖ M)

lemma spectatorLift_one (R k r : ℕ) :
 spectatorLift R k r (1 : Matrix (Fin (R*2^k)) (Fin (R*2^k)) ℂ)=1 := by
 unfold spectatorLift
 rw [Matrix.one_kronecker_one]
 exact (Matrix.reindexAlgEquiv ℂ ℂ (spectatorCoordinates R k r)).map_one
lemma spectatorLift_mul (R k r : ℕ) (M N : Matrix (Fin (R*2^k)) (Fin (R*2^k)) ℂ) :
 spectatorLift R k r (M*N)=spectatorLift R k r M*spectatorLift R k r N := by
 unfold spectatorLift
 rw [←PaddingWords.reindex_mul,←Matrix.mul_kronecker_mul,Matrix.one_mul]


lemma spectatorLift_array (R k r : ℕ)
 (M : Matrix (Fin (R*2^k)) (Fin (R*2^k)) ℂ)
 (X : Fin (R*2^(k+r))→ℂ) (s : Fin (2^r)) (j : Fin (R*2^k)) :
 (spectatorLift R k r M).mulVec X (spectatorCoordinates R k r (s,j))=
 M.mulVec (fun y => X (spectatorCoordinates R k r (s,y))) j := by
 unfold spectatorLift Matrix.mulVec dotProduct
 rw [←(spectatorCoordinates R k r).sum_comp,Fintype.sum_prod_type]
 simp [Matrix.reindex_apply,Matrix.one_apply]

lemma copies_array (R k : ℕ) (M : Matrix (Fin (2^k)) (Fin (2^k)) ℂ)
 (X : Fin R→Fin (2^k)→ℂ) (i : Fin R) (z : Fin (2^k)) :
 (PaddingWords.copiesMatrix R k M).mulVec (RoleWords.arrayValues k X)
 (RoleWords.roleAddresses R k (i,z))=M.mulVec (X i) z := by
 unfold PaddingWords.copiesMatrix Matrix.mulVec dotProduct
 rw [←(RoleWords.roleAddresses R k).sum_comp,Fintype.sum_prod_type]
 simp [Matrix.reindex_apply,Matrix.one_apply]

lemma spectator_copies_array (R k r : ℕ)
 (M : Matrix (Fin (2^k)) (Fin (2^k)) ℂ)
 (X : Fin R→Fin (2^(k+r))→ℂ) (i : Fin R) (s : Fin (2^r)) (z : Fin (2^k)) :
 (spectatorLift R k r (PaddingWords.copiesMatrix R k M)).mulVec
 (RoleWords.arrayValues (k+r) X)
 (RoleWords.roleAddresses R (k+r) (i,(spectatorSplit k r).symm (s,z)))=
 M.mulVec (fun y => X i ((spectatorSplit k r).symm (s,y))) z := by
 rw [←spectatorCoordinates_at,spectatorLift_array]
 have data :
  (fun y => RoleWords.arrayValues (k+r) X (spectatorCoordinates R k r (s,y)))=
  RoleWords.arrayValues k (fun i y => X i ((spectatorSplit k r).symm (s,y))) := by
  funext y
  obtain ⟨⟨j,y⟩,rfl⟩ := (RoleWords.roleAddresses R k).surjective y
  rw [spectatorCoordinates_at,RoleWords.arrayValues_at,RoleWords.arrayValues_at]
 rw [data,copies_array]

end
end ExactFourierCircuits.UniformNativeScheduleMatrix

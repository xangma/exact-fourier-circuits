import UniformNativeTerminalExchange
import UniformNativeLowXor
import UniformPhysicalTensorSplit
import UniformNativeYRecordMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformNativeTerminalY
open OAI.ExactFourier UniformMachine BinaryFrames
open UniformNativeScheduleMatrix UniformNativeRoleSemantics UniformNativeRecordRoles
open UniformNativeResidualSemantics UniformNativeCopiedInverse UniformBinaryXorCoordinates
open UniformNativeScalarAlgebra UniformNativeTerminalExchange
open scoped BigOperators
namespace Y
export UniformNativeYRecordMachine (Direction values actions actions_cons)
end Y
noncomputable section
variable {δ β : Type*} {w R V : ℕ}
local instance : DecidableEq δ := Classical.decEq δ

lemma reindex_action {N : ℕ} (e : Fin N≃Fin N) (M : Matrix (Fin N) (Fin N) ℂ)
 (X : Fin N→ℂ) (i : Fin N) :
 (Matrix.reindex e e M).mulVec X (e i)=M.mulVec (fun j=>X (e j)) i := by
 unfold Matrix.mulVec dotProduct
 rw [←e.sum_comp]
 simp [Matrix.reindex_apply]

lemma original_points (e : TerminalWords.Role δ β≃Fin w) (k : ℕ)
 (r : TerminalWords.Role δ β) (x : Vec (Fin k)) :
 originalCoordinates w k (TerminalWords.points e k (r,x))=
 RoleWords.roleAddresses w k (e r,encode x) := by
 simp [originalCoordinates,TerminalWords.points,originalToNative,encode]

lemma encode_add (k : ℕ) (z : Fin (2^k)) (u : Vec (Fin k)) :
 encode (binaryCoordinates k z+u)=xorIndex z (encode u) := by
 apply (binaryCoordinates k).injective
 simp [encode,xor_coordinates]

/-- The compiled original-address Y matrix is the real integer-XOR action
in little-endian native coordinates. -/
theorem original_translation_bank (e : TerminalWords.Role δ β≃Fin w) (k : ℕ)
 (u : δ→Vec (Fin k)) (X : Fin (w*2^k)→ℂ) (b : Fin 2) (d : δ) (z : Fin (2^k)) :
 (Matrix.reindex (originalCoordinates w k) (originalCoordinates w k)
  (TerminalWords.translationMatrix e u)).mulVec X
  (RoleWords.roleAddresses w k (e (.inl (b,d)),z))=
 if b=0 then X (RoleWords.roleAddresses w k (e (.inl (b,d)),z))
 else X (RoleWords.roleAddresses w k (e (.inl (b,d)),xorIndex z (encode (u d)))) := by
 have idx:originalCoordinates w k (TerminalWords.points e k (.inl (b,d),binaryCoordinates k z))=
  RoleWords.roleAddresses w k (e (.inl (b,d)),z) := by simp [original_points,encode]
 rw [←idx,reindex_action,TerminalWords.translationMatrix,TerminalWords.monomial_apply,one_mul]
 simp only [TerminalWords.packedPerm,Equiv.trans_apply,Equiv.symm_apply_apply,
  TerminalWords.translateYEquiv_apply]
 have enc:encode (binaryCoordinates k z)=z:=by simp [encode]
 fin_cases b <;> simp [TerminalWords.translateY,original_points,encode_add,enc]

theorem original_translation_aux (e : TerminalWords.Role δ β≃Fin w) (k : ℕ)
 (u : δ→Vec (Fin k)) (X : Fin (w*2^k)→ℂ) (a : β) (z : Fin (2^k)) :
 (Matrix.reindex (originalCoordinates w k) (originalCoordinates w k)
  (TerminalWords.translationMatrix e u)).mulVec X
  (RoleWords.roleAddresses w k (e (.inr a),z))=
 X (RoleWords.roleAddresses w k (e (.inr a),z)) := by
 have idx:originalCoordinates w k (TerminalWords.points e k (.inr a,binaryCoordinates k z))=
  RoleWords.roleAddresses w k (e (.inr a),z) := by simp [original_points,encode]
 rw [←idx,reindex_action,TerminalWords.translationMatrix,TerminalWords.monomial_apply,one_mul]
 simp [TerminalWords.packedPerm,TerminalWords.translateY,original_points,encode]

def lowIndex (k rest : ℕ) (z : Fin (2^k)) : Fin (2^(k+rest)) :=
 z.castLE (Nat.pow_le_pow_right (by decide) (Nat.le_add_right k rest))

lemma spectator_xor (k rest : ℕ) (s : Fin (2^rest)) (z a : Fin (2^k)) :
 xorIndex ((spectatorSplit k rest).symm (s,z)) (lowIndex k rest a)=
 (spectatorSplit k rest).symm (s,xorIndex z a) := by
 apply Fin.ext
 simp only [xorIndex,Fin.val_mk,lowIndex,Fin.val_castLE,
  UniformPhysicalTensorSplit.split_address]
 simpa [Nat.mul_comm,Nat.add_comm] using
  UniformNativeLowXor.low_xor k s.val z.val a.val z.isLt a.isLt

def direction (e : TerminalWords.Role δ β↪Fin R) {n : ℕ}
 (u : δ→Vec (Fin n)) (d : δ) : Y.Direction R n := ⟨e (.inl (1,d)),u d⟩
def directions (e : TerminalWords.Role δ β↪Fin R) {n : ℕ}
 (u : δ→Vec (Fin n)) (L : List δ) : List (Y.Direction R n) := L.map (direction e u)

lemma values_bank (e : TerminalWords.Role δ β↪Fin R) (q n rest : ℕ)
 (u : δ→Vec (Fin n)) (a d : δ) (f : Fin R→Fin (2^(q*n+rest))→Scalar)
 (b : Fin 2) (z : Fin (2^(q*n+rest))) :
 Y.values q n (q*n+rest) (direction e u a) f (e (.inl (b,d))) z=
 if b=1 ∧ d=a then f (e (.inl (b,d)))
  (xorIndex z (lowIndex (q*n) rest (encode (ColumnTerminalFlat.direction q (u d)))))
 else f (e (.inl (b,d))) z := by
 have bound:(encode (ColumnTerminalFlat.direction q (u a))).val<2^(q*n+rest):=
  lt_of_lt_of_le (encode (ColumnTerminalFlat.direction q (u a))).isLt
   (Nat.pow_le_pow_right (by decide) (Nat.le_add_right (q*n) rest))
 by_cases hd:d=a
 · subst d
   fin_cases b <;>
    simp [UniformNativeYRecordMachine.values,direction,e.injective.eq_iff,
     UniformResidualNativeTranslationMachine.translated,UniformResidualNativeTranslationMachine.partner,
     UniformResidualNativeTranslationMachine.volume,Nat.mod_eq_of_lt bound,xorIndex,lowIndex]
 · fin_cases b <;> simp [UniformNativeYRecordMachine.values,direction,e.injective.eq_iff,hd]

lemma values_outside (e : TerminalWords.Role δ β↪Fin R) (q n k : ℕ)
 (u : δ→Vec (Fin n)) (a : δ) (f : Fin R→Fin (2^k)→Scalar)
 (i : Fin R) (hi:∀d,i≠e (.inl (1,d))) (z : Fin (2^k)) :
 Y.values q n k (direction e u a) f i z=f i z := by
 simp [UniformNativeYRecordMachine.values,direction,hi]

theorem actions_bank (e : TerminalWords.Role δ β↪Fin R) (q n rest : ℕ)
 (u : δ→Vec (Fin n)) (L : List δ) (hn:L.Nodup)
 (f : Fin R→Fin (2^(q*n+rest))→Scalar) (d : δ) (b : Fin 2) (z : Fin (2^(q*n+rest))) :
 Y.actions q n (q*n+rest) (directions e u L) f (e (.inl (b,d))) z=
 if b=1 ∧ d∈L then f (e (.inl (b,d)))
  (xorIndex z (lowIndex (q*n) rest (encode (ColumnTerminalFlat.direction q (u d)))))
 else f (e (.inl (b,d))) z := by
 classical
 induction L generalizing f z with
 | nil=>
  simp only [List.not_mem_nil,and_false,ite_false]
  rfl
 | cons a L ih=>
  rw [List.nodup_cons] at hn
  change Y.actions q n (q*n+rest) (directions e u L)
   (Y.values q n (q*n+rest) (direction e u a) f) (e (.inl (b,d))) z=_
  erw [ih hn.2]
  by_cases hd:d=a
  · subst d
    fin_cases b <;> simp [hn.1,values_bank]
  · fin_cases b <;> simp [hd,values_bank]

theorem actions_outside (e : TerminalWords.Role δ β↪Fin R) (q n k : ℕ)
 (u : δ→Vec (Fin n)) (L : List δ) (f : Fin R→Fin (2^k)→Scalar)
 (i : Fin R) (hi:∀d,i≠e (.inl (1,d))) (z : Fin (2^k)) :
 Y.actions q n k (directions e u L) f i z=f i z := by
 induction L generalizing f with
 | nil=>rfl
 | cons a L ih=>
  change Y.actions q n k (directions e u L) (Y.values q n k (direction e u a) f) i z=_
  erw [ih]
  exact values_outside e q n k u a f i hi z

/-- Native low-block translation, active-role padding and high spectators agree
with the real opcode3 direction-list fold on arbitrary dirty role arrays. -/
theorem native_active_translation_values [Fintype δ]
 (e : TerminalWords.Role δ β≃Fin w) (p q n rest : ℕ) (hw:w≤2^p)
 (u : δ→Vec (Fin n)) (f : Fin (2^p)→Fin (2^(q*n+rest))→Scalar) :
 (spectatorLift (2^p) (q*n) rest (nativeMatrix (2^p) (q*n)
  (wordMatrix (TensorWords.embeddedWord (paddingAddress w p (q*n) hw)
   (PaddingWords.canonicalNetworkWord w (q*n)
    [.monomial (TerminalWords.translationMatrix e (fun d=>ColumnTerminalFlat.direction q (u d)))
     (TerminalWords.translationMatrix_monomial e _)]))))).mulVec
 (RoleWords.arrayValues (q*n+rest) (fun i a=>(f i a).value))=
 RoleWords.arrayValues (q*n+rest) (fun i a=>(Y.actions q n (q*n+rest)
  (directions (e.toEmbedding.trans (paddingRole w p hw)) u Finset.univ.toList) f i a).value) := by
 classical
 let j:=paddingRole w p hw
 let U:=fun d=>ColumnTerminalFlat.direction q (u d)
 have native:
  nativeMatrix (2^p) (q*n)
   (wordMatrix (TensorWords.embeddedWord (paddingAddress w p (q*n) hw)
    (PaddingWords.canonicalNetworkWord w (q*n)
     [.monomial (TerminalWords.translationMatrix e U)
      (TerminalWords.translationMatrix_monomial e U)])))=
  Embedded.matrix (TripleSchedule.Global.addressEmbedding (n:=q*n) j)
   (Matrix.reindex (originalCoordinates w (q*n)) (originalCoordinates w (q*n))
    (TerminalWords.translationMatrix e U)) := by
  rw [TensorWords.embeddedWord_matrix,paddingAddress_role,native_embedding,native_canonical_matrix]
  simp [wordMatrix,WordStep.matrix,j]
 rw [native]
 funext x
 obtain ⟨⟨i,a⟩,rfl⟩:=(RoleWords.roleAddresses (2^p) (q*n+rest)).surjective x
 obtain ⟨⟨s,z⟩,rfl⟩:=(spectatorSplit (q*n) rest).symm.surjective a
 rw [←spectatorCoordinates_at,spectatorLift_array,spectatorCoordinates_at,RoleWords.arrayValues_at]
 by_cases hi:i∈Set.range j
 · obtain ⟨i,rfl⟩:=hi
   rw [←TripleSchedule.Global.addressEmbedding_at,TripleSchedule.Global.embedded_selected]
   obtain ⟨r,rfl⟩:=e.surjective i
   cases r with
   | inl bd=>
    rcases bd with ⟨b,d⟩
    rw [original_translation_bank]
    change _=(Y.actions q n (q*n+rest)
     (directions (e.toEmbedding.trans j) u Finset.univ.toList) f
     ((e.toEmbedding.trans j) (.inl (b,d))) ((spectatorSplit (q*n) rest).symm (s,z))).value
    erw [actions_bank _ _ _ _ _ _ (Finset.nodup_toList _)]
    fin_cases b <;> simp [TripleSchedule.Global.addressEmbedding_at,spectatorCoordinates_at,
     RoleWords.arrayValues_at,spectator_xor,U]
   | inr a=>
    rw [original_translation_aux]
    have outside:∀d,j (e (.inr a))≠(e.toEmbedding.trans j) (.inl (1,d)) := by
     intro d h
     have eq:=e.injective (j.injective h)
     cases eq
    erw [actions_outside (e.toEmbedding.trans j) q n (q*n+rest) u Finset.univ.toList f _ outside]
    rw [TripleSchedule.Global.addressEmbedding_at,spectatorCoordinates_at,RoleWords.arrayValues_at]
 · rw [TripleSchedule.Global.embedded_untouched _ _ _ _
    (TripleSchedule.Global.addressEmbedding_not_mem j i hi z)]
   have outside:∀d,i≠(e.toEmbedding.trans j) (.inl (1,d)):=by
    intro d eq
    exact hi ⟨e (.inl (1,d)),eq.symm⟩
   erw [actions_outside (e.toEmbedding.trans j) q n (q*n+rest) u Finset.univ.toList f _ outside]
   rw [spectatorCoordinates_at,RoleWords.arrayValues_at]

end
end ExactFourierCircuits.UniformNativeTerminalY

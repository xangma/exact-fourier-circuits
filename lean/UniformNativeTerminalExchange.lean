import UniformNativeScalarAlgebra
import UniformNativeExchangeRecordMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformNativeTerminalExchange
open OAI.ExactFourier UniformMachine
open UniformNativeScheduleMatrix UniformNativeRoleSemantics UniformNativeRecordRoles
open UniformNativeScalarAlgebra
open scoped BigOperators
namespace E
export UniformFixedNetworkExchangeChildMachine (values negative)
end E
namespace Rec
export UniformNativeExchangeRecordMachine (Pair actions actions_cons)
end Rec
noncomputable section
variable {δ β : Type*} {w R V : ℕ}
local instance : DecidableEq δ := Classical.decEq δ

def pair (e : TerminalWords.Role δ β ↪ Fin R) (d : δ) : Rec.Pair R :=
 ⟨e (.inl (0,d)),e (.inl (1,d)),fun h=>by
  have eq:=e.injective h
  have zero:(0:Fin 2)=1:=congrArg (fun x=>x.1) (Sum.inl.inj eq)
  exact (by decide : (0:Fin 2)≠1) zero⟩

def pairs (e : TerminalWords.Role δ β ↪ Fin R) (L : List δ) : List (Rec.Pair R) := L.map (pair e)

lemma values_bank (e : TerminalWords.Role δ β ↪ Fin R) (a d : δ)
 (f : Fin R→Fin V→Scalar) (b : Fin 2) (z : Fin V) :
 E.values (pair e a).first (pair e a).second f (e (.inl (b,d))) z=
 if d=a then (if b=0 then f (e (.inl (1,d))) z else E.negative (f (e (.inl (0,d))) z))
 else f (e (.inl (b,d))) z := by
 classical
 by_cases h:d=a
 · subst d
   fin_cases b <;> simp [UniformFixedNetworkExchangeChildMachine.values,pair,e.injective.eq_iff]
 · fin_cases b <;> simp [UniformFixedNetworkExchangeChildMachine.values,pair,e.injective.eq_iff,h]

lemma values_outside (e : TerminalWords.Role δ β ↪ Fin R) (a : δ)
 (f : Fin R→Fin V→Scalar) (i : Fin R) (hi:∀b d,i≠e (.inl (b,d))) (z : Fin V) :
 E.values (pair e a).first (pair e a).second f i z=f i z := by
 simp [UniformFixedNetworkExchangeChildMachine.values,pair,hi]

theorem actions_bank (e : TerminalWords.Role δ β ↪ Fin R) (L : List δ) (hn:L.Nodup)
 (f : Fin R→Fin V→Scalar) (d : δ) (b : Fin 2) (z : Fin V) :
 Rec.actions (pairs e L) f (e (.inl (b,d))) z=
 if d∈L then (if b=0 then f (e (.inl (1,d))) z else E.negative (f (e (.inl (0,d))) z))
 else f (e (.inl (b,d))) z := by
 classical
 induction L generalizing f with
 | nil => simp [pairs,UniformNativeExchangeRecordMachine.actions]
 | cons a L ih =>
  rw [List.nodup_cons] at hn
  rw [pairs,List.map_cons,Rec.actions_cons]
  rw [show L.map (pair e)=pairs e L from rfl,ih hn.2]
  by_cases hd:d=a
  · subst d
    simp [hn.1,values_bank]
  · fin_cases b <;> simp [hd,values_bank]

theorem actions_outside (e : TerminalWords.Role δ β ↪ Fin R) (L : List δ)
 (f : Fin R→Fin V→Scalar) (i : Fin R) (hi:∀b d,i≠e (.inl (b,d))) (z : Fin V) :
 Rec.actions (pairs e L) f i z=f i z := by
 induction L generalizing f with
 | nil => rfl
 | cons a L ih =>
  rw [pairs,List.map_cons,Rec.actions_cons]
  rw [show L.map (pair e)=pairs e L from rfl,ih]
  exact values_outside e a f i hi z

/-- Signed bank exchange is a pointwise role matrix in every address convention. -/
def rolePerm (e : TerminalWords.Role δ β ≃ Fin w) : Equiv.Perm (Fin w) :=
 e.symm.trans ((Equiv.sumCongr ((Equiv.swap (0:Fin 2) 1).prodCongr (Equiv.refl δ))
  (Equiv.refl β)).trans e)
def roleSign (e : TerminalWords.Role δ β ≃ Fin w) (i : Fin w) : ℂ :=
 match e.symm i with
 | .inl (b,_) => if b=0 then 1 else -1
 | .inr _ => 1
def roleMatrix (e : TerminalWords.Role δ β ≃ Fin w) : Matrix (Fin w) (Fin w) ℂ :=
 fun i j=>if j=rolePerm e i then roleSign e i else 0

lemma roleMatrix_apply (e : TerminalWords.Role δ β ≃ Fin w) (X : Fin w→ℂ) (i : Fin w) :
 (roleMatrix e).mulVec X i=roleSign e i*X (rolePerm e i) := by
 classical
 simp [roleMatrix,Matrix.mulVec,dotProduct,ite_mul]

theorem exchange_pointwise (e : TerminalWords.Role δ β ≃ Fin w) (k : ℕ) :
 TerminalWords.exchangeMatrix e k=RoleWords.pointwiseMatrix k (roleMatrix e) := by
 classical
 ext x y
 obtain ⟨⟨i,a⟩,rfl⟩:=(RoleWords.roleAddresses w k).surjective x
 obtain ⟨⟨j,b⟩,rfl⟩:=(RoleWords.roleAddresses w k).surjective y
 obtain ⟨r,rfl⟩:=e.surjective i
 cases r with
 | inl rd =>
  rcases rd with ⟨bank,d⟩
  fin_cases bank <;>
   simp [TerminalWords.exchangeMatrix,TerminalWords.monomial,TerminalWords.packedPerm,
    TerminalWords.points,TerminalWords.exchangePoint,TerminalWords.exchangeSign,
    TerminalWords.exchangeEquiv_apply,RoleWords.pointwiseMatrix,roleMatrix,roleSign,rolePerm,
    Matrix.reindex_apply,Matrix.one_apply,Prod.mk.injEq,and_comm,eq_comm,ite_and]
 | inr aux =>
  simp [TerminalWords.exchangeMatrix,TerminalWords.monomial,TerminalWords.packedPerm,
   TerminalWords.points,TerminalWords.exchangePoint,TerminalWords.exchangeSign,
   TerminalWords.exchangeEquiv_apply,RoleWords.pointwiseMatrix,roleMatrix,roleSign,rolePerm,
   Matrix.reindex_apply,Matrix.one_apply,Prod.mk.injEq,and_comm,eq_comm,ite_and]

/-- The actual complete list of distinct signed exchanges has the terminal role action. -/
theorem actions_roleMatrix [Fintype δ] (e : TerminalWords.Role δ β ≃ Fin w)
 (j : Fin w↪Fin R) (f : Fin R→Fin V→Scalar) (i : Fin R) (z : Fin V) :
 (Embedded.matrix j (roleMatrix e)).mulVec (fun a=>(f a z).value) i=
 (Rec.actions (pairs (e.toEmbedding.trans j) Finset.univ.toList) f i z).value := by
 classical
 by_cases hi:i∈Set.range j
 · obtain ⟨i,rfl⟩:=hi
   rw [TripleSchedule.Global.embedded_selected,roleMatrix_apply]
   obtain ⟨r,rfl⟩:=e.surjective i
   cases r with
   | inl bd =>
    rcases bd with ⟨b,d⟩
    rw [show j (e (.inl (b,d)))=(e.toEmbedding.trans j) (.inl (b,d)) from rfl,
     actions_bank _ _ (Finset.nodup_toList _)]
    fin_cases b <;> simp [roleSign,rolePerm,UniformFixedNetworkExchangeChildMachine.negative]
   | inr a =>
    have outside:∀b d,j (e (.inr a))≠(e.toEmbedding.trans j) (.inl (b,d)) := by
     intro b d h
     have eq:=e.injective (j.injective h)
     cases eq
    rw [actions_outside _ _ _ _ outside]
    simp [roleSign,rolePerm]
 · rw [TripleSchedule.Global.embedded_untouched _ _ _ _ hi]
   have outside:∀b d,i≠(e.toEmbedding.trans j) (.inl (b,d)):=by
    intro b d eq
    exact hi ⟨e (.inl (b,d)),eq.symm⟩
   rw [actions_outside _ _ _ _ outside]

/-- Literal canonical/padded terminal exchange has exactly the actual bank-pair fold,
including arbitrary unused roles and every high spectator slice. -/
theorem native_active_exchange_values [Fintype δ]
 (e : TerminalWords.Role δ β ≃ Fin w) (p k rest : ℕ) (hw:w≤2^p)
 (f : Fin (2^p)→Fin (2^(k+rest))→Scalar) :
 (spectatorLift (2^p) k rest (nativeMatrix (2^p) k
  (wordMatrix (TensorWords.embeddedWord (paddingAddress w p k hw)
   (PaddingWords.canonicalNetworkWord w k
    [.monomial (TerminalWords.exchangeMatrix e k) (TerminalWords.exchangeMatrix_monomial e k)]))))).mulVec
 (RoleWords.arrayValues (k+rest) (fun i a=>(f i a).value))=
 RoleWords.arrayValues (k+rest) (fun i a=>(Rec.actions
  (pairs (e.toEmbedding.trans (paddingRole w p hw)) Finset.univ.toList) f i a).value) := by
 have native:
  nativeMatrix (2^p) k
   (wordMatrix (TensorWords.embeddedWord (paddingAddress w p k hw)
    (PaddingWords.canonicalNetworkWord w k
     [.monomial (TerminalWords.exchangeMatrix e k) (TerminalWords.exchangeMatrix_monomial e k)])))=
  RoleWords.pointwiseMatrix k (Embedded.matrix (paddingRole w p hw) (roleMatrix e)) := by
  rw [TensorWords.embeddedWord_matrix,paddingAddress_role,native_embedding,native_canonical_matrix]
  have singleton:wordMatrix (A:=C) [.monomial (TerminalWords.exchangeMatrix e k)
   (TerminalWords.exchangeMatrix_monomial e k)]=TerminalWords.exchangeMatrix e k := by
   simp [wordMatrix,WordStep.matrix]
  rw [singleton,exchange_pointwise,original_pointwise,pointwise_embedding]
 rw [native]
 funext x
 obtain ⟨⟨i,a⟩,rfl⟩:=(RoleWords.roleAddresses (2^p) (k+rest)).surjective x
 obtain ⟨⟨s,z⟩,rfl⟩:=(UniformNativeCopiedInverse.spectatorSplit k rest).symm.surjective a
 rw [spectator_pointwise_array,RoleWords.arrayValues_at]
 exact actions_roleMatrix e (paddingRole w p hw) f i _

end
end ExactFourierCircuits.UniformNativeTerminalExchange

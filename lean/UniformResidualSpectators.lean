import UniformResidualPermutation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualSpectators
open BinaryFrames UniformBinaryXorCoordinates UniformResidualPermutation
noncomputable section
/-- The remaining r high bits are spectator coordinates. Lower q selected
bits stay innermost; this is an explicit arithmetic equivalence. -/
def split (k r:ℕ) : Fin (2^(k+r))≃Fin (2^r)×Fin (2^k) :=
 (finCongr (by rw [Nat.pow_add];ring)).trans finProdFinEquiv.symm
def extend (k r:ℕ) (F:Fin (2^k)≃Fin (2^k)) : Fin (2^(k+r))≃Fin (2^(k+r)) :=
 (split k r).trans ((Equiv.refl _).prodCongr F) |>.trans (split k r).symm
lemma split_values (k r:ℕ) (j:Fin (2^(k+r))) :
 ((split k r j).1.val,(split k r j).2.val)=(j.val/2^k,j.val%2^k) := by simp [split,finProdFinEquiv]
lemma extend_value (k r:ℕ) (F:Fin (2^k)≃Fin (2^k)) (j:Fin (2^(k+r))) :
 (extend k r F j).val=(F (split k r j).2).val+2^k*(j.val/2^k) := by
 simp [extend,split,finProdFinEquiv]
lemma extend_zero (k r:ℕ) (F:Fin (2^k)≃Fin (2^k)) (zero:F 0=0) : extend k r F 0=0 := by
 apply Fin.ext
 rw [extend_value]
 have lo : (split k r (0:Fin (2^(k+r)))).2 = 0 := by apply Fin.ext; simp [split,finProdFinEquiv]
 rw [lo,zero]
 simp
lemma extend_xor (k r:ℕ) (F:Fin (2^k)≃Fin (2^k))
 (add:∀a b,F (xorIndex a b)=xorIndex (F a) (F b)) (a b:Fin (2^(k+r))) :
 extend k r F (xorIndex a b)=xorIndex (extend k r F a) (extend k r F b) := by
 have spl : split k r (xorIndex a b)=
  (xorIndex (split k r a).1 (split k r b).1,xorIndex (split k r a).2 (split k r b).2) := by
  apply Prod.ext <;> apply Fin.ext
  · simpa [split,finProdFinEquiv,xorIndex] using Nat.xor_div_two_pow (a:=a.val) (b:=b.val) (n:=k)
  · simpa [split,finProdFinEquiv,xorIndex] using Nat.xor_mod_two_pow (a:=a.val) (b:=b.val) (n:=k)
 apply (split k r).injective
 have lhs : split k r (extend k r F (xorIndex a b))=
  ((split k r (xorIndex a b)).1,F (split k r (xorIndex a b)).2) := by simp [extend,Prod.map]
 rw [lhs,spl]
 have sa:split k r (extend k r F a)=((split k r a).1,F (split k r a).2):=by simp [extend,Prod.map]
 have sb:split k r (extend k r F b)=((split k r b).1,F (split k r b).2):=by simp [extend,Prod.map]
 have splitxor : split k r (xorIndex (extend k r F a) (extend k r F b))=
  (xorIndex (split k r (extend k r F a)).1 (split k r (extend k r F b)).1,
   xorIndex (split k r (extend k r F a)).2 (split k r (extend k r F b)).2) := by
  apply Prod.ext <;> apply Fin.ext
  · simpa [split,finProdFinEquiv,xorIndex] using Nat.xor_div_two_pow (a:=(extend k r F a).val) (b:=(extend k r F b).val) (n:=k)
  · simpa [split,finProdFinEquiv,xorIndex] using Nat.xor_mod_two_pow (a:=(extend k r F a).val) (b:=(extend k r F b).val) (n:=k)
 rw [splitxor,sa,sb,add]

lemma extend_low (k r:ℕ) (F:Fin (2^k)≃Fin (2^k)) (j:Fin (2^k)) :
 (extend k r F ⟨j.val,j.isLt.trans_le (Nat.pow_le_pow_right (by omega) (by omega))⟩).val=(F j).val := by
 rw [extend_value]
 have pair : split k r (⟨j.val,j.isLt.trans_le (Nat.pow_le_pow_right (by omega) (by omega))⟩:Fin (2^(k+r)))=(0,j) := by
  apply Prod.ext <;> apply Fin.ext <;> simp [split,finProdFinEquiv,Nat.div_eq_of_lt j.isLt,Nat.mod_eq_of_lt j.isLt]
 rw [pair]
 simp [Nat.div_eq_of_lt j.isLt]

/-- Appended spectator unit images are literal powers of two. -/
lemma extend_high_unit (k r:ℕ) (F:Fin (2^k)≃Fin (2^k)) (zero:F 0=0) (i:Fin r) :
 (extend k r F (encode (unit (⟨k+i.val,by omega⟩:Fin (k+r))))).val=2^(k+i.val) := by
 rw [extend_value]
 have pair : split k r (encode (unit (⟨k+i.val,by omega⟩:Fin (k+r))))=(encode (unit i),0) := by
  apply Prod.ext <;> apply Fin.ext <;> simp [split,finProdFinEquiv,encode_unit,Nat.pow_add]
 rw [pair,zero]
 simp [encode_unit,Nat.pow_add]

end
end ExactFourierCircuits.UniformResidualSpectators

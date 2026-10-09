import UniformResidualFiberTraversal
import UniformResidualNativeCoordinates
import UniformResidualBasisMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualPermutation
open BinaryFrames UniformResidualNativeCoordinates UniformBinaryXorCoordinates
open UniformResidualFiberTraversal
open scoped BigOperators
noncomputable section

lemma encode_unit {k : ℕ} (i : Fin k) : (encode (unit i)).val=2^i.val := by
 rw [encode_value]
 simp [unit,apply_ite]
 rfl

lemma xor_high (h a : ℕ) (small : a<2^h) : a^^^2^h=a+2^h := by
 have positive:=Nat.two_pow_pos h
 have parts:=Nat.mod_add_div (a^^^2^h) (2^h)
 rw [Nat.xor_mod_two_pow,Nat.xor_div_two_pow,Nat.mod_eq_of_lt small,
  Nat.div_eq_of_lt small,Nat.mod_self,Nat.div_self positive] at parts
 simpa [Nat.xor_zero,Nat.zero_xor] using parts.symm

/-- Actual native address output of the DFS is determined by its physically
supplied unit images. This is a pure identification lemma, not a RAM callback. -/
theorem address_of_xor_equiv {k : ℕ} (F : Fin (2^k)≃Fin (2^k))
 (zero : F 0=0) (add : ∀a b,F (xorIndex a b)=xorIndex (F a) (F b))
 (image : ℕ→ℕ) (bank : ∀i:Fin k,image i.val=(F (encode (unit i))).val)
 (h a j : ℕ) (hk : h≤k) (js : j<2^h) :
 address image h a j=a^^^(F ⟨j,js.trans_le (Nat.pow_le_pow_right (by omega : 1≤2) hk)⟩).val := by
 induction h generalizing a j with
 | zero=>
   have j0:j=0:=by simpa using js
   subst j
   simp [address,zero]
 | succ h ih=>
   have hlt:h<k:=by omega
   have ph:2^h<2^k:=Nat.pow_lt_pow_right (by omega : 1<2) hlt
   by_cases jl:j<2^h
   · simpa [address,jl] using ih a j (by omega) jl
   · have jl':j-2^h<2^h:=by rw [Nat.pow_succ] at js;omega
     have eqj : (j-2^h)^^^2^h=j:=by rw [xor_high h _ jl'];omega
     let low : Fin (2^k):=⟨j-2^h,jl'.trans_le (Nat.pow_le_pow_right (by omega : 1≤2) (by omega : h≤k))⟩
     let high : Fin (2^k):=encode (unit (⟨h,hlt⟩:Fin k))
     have highValue:high.val=2^h:=encode_unit _
     have split : xorIndex low high=⟨j,js.trans_le (Nat.pow_le_pow_right (by omega : 1≤2) hk)⟩ := by
      apply Fin.ext
      simpa [low,xorIndex,highValue] using eqj
     have hF:=congrArg Fin.val (add low high)
     rw [split] at hF
     simp only [xorIndex,Fin.val_mk] at hF
     rw [address,ite_eq_right jl,ih (a^^^image h) (j-2^h) (by omega) jl',bank ⟨h,hlt⟩]
     rw [hF]
     simp [low,high,Nat.xor_comm,Nat.xor_left_comm]

/-- Native representative-major, selected-bit-minor input order. -/
def splitInput (q w : ℕ) : Fin (2^(q*(w+1)))≃Fin (2^(q*w))×Fin (2^q) :=
 (finCongr (by rw [←Nat.pow_add];congr 1)).trans finProdFinEquiv.symm

def permutation (q w : ℕ) (v : Vec (Fin (w+1))) (p : Fin (w+1)) (hp : v p=1) :
 Fin (2^(q*(w+1)))≃Fin (2^(q*(w+1))) := (splitInput q w).trans (nativeFiber q w v p hp)

lemma split_values (q w : ℕ) (a : Fin (2^(q*(w+1)))) :
 ((splitInput q w a).1.val,(splitInput q w a).2.val)=(a.val/2^q,a.val%2^q) := by
 simp [splitInput,finProdFinEquiv]

lemma permutation_zero (q w : ℕ) (v : Vec (Fin (w+1))) (p : Fin (w+1)) (hp : v p=1) :
 permutation q w v p hp 0=0 := by
 have split : splitInput q w 0=(0,0) := by
  apply Prod.ext <;> apply Fin.ext <;> simp [splitInput,finProdFinEquiv]
 simp [permutation,split]

lemma permutation_xor (q w : ℕ) (v : Vec (Fin (w+1))) (p : Fin (w+1)) (hp : v p=1)
 (a b : Fin (2^(q*(w+1)))) :
 permutation q w v p hp (xorIndex a b)=xorIndex (permutation q w v p hp a) (permutation q w v p hp b) := by
 have split : splitInput q w (xorIndex a b)=
  (xorIndex (splitInput q w a).1 (splitInput q w b).1,
   xorIndex (splitInput q w a).2 (splitInput q w b).2) := by
  apply Prod.ext <;> apply Fin.ext
  · simpa [splitInput,finProdFinEquiv,xorIndex] using Nat.xor_div_two_pow (a:=a.val) (b:=b.val) (n:=q)
  · simpa [splitInput,finProdFinEquiv,xorIndex] using Nat.xor_mod_two_pow (a:=a.val) (b:=b.val) (n:=q)
 simpa [permutation,split] using nativeFiber_xor q w v p hp
  (splitInput q w a).1 (splitInput q w b).1 (splitInput q w a).2 (splitInput q w b).2


lemma copy_value (q m : ℕ) (v : Vec (Fin m)) (c : Fin q) :
 (encode (UniformResidualFibers.copyVector q v c)).val=2^(c.val*m)*(encode v).val := by
 rw [encode_value]
 rw [←(finProdFinEquiv : Fin q×Fin m≃Fin (q*m)).sum_comp,Fintype.sum_prod_type]
 simp only [UniformResidualFibers.copyVector,UniformResidualFibers.copyCombination_apply]
 simp only [unit,ite_mul,one_mul,zero_mul,apply_ite]
 rw [Finset.sum_comm]
 simp [finProdFinEquiv]
 rw [encode_value]
 simp_rw [Nat.pow_add]
 rw [Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro i _
 ring

lemma split_selected (q w : ℕ) (c : Fin q) :
 splitInput q w (encode (unit (⟨c.val,by rw [Nat.mul_add,Nat.mul_one];have h:=c.isLt;omega⟩:Fin (q*(w+1)))))=
 (0,encode (unit c)) := by
 apply Prod.ext <;> apply Fin.ext
 · have small:=Nat.pow_lt_pow_right (by omega : 1<2) c.isLt
   simp [splitInput,finProdFinEquiv,encode_unit,Nat.div_eq_of_lt small]
 · have small:=Nat.pow_lt_pow_right (by omega : 1<2) c.isLt
   simp [splitInput,finProdFinEquiv,encode_unit,Nat.mod_eq_of_lt small]

lemma split_representative (q w : ℕ) (i : Fin (q*w)) :
 splitInput q w (encode (unit (⟨q+i.val,by rw [Nat.mul_add,Nat.mul_one];have h:=i.isLt;omega⟩:Fin (q*(w+1)))))=
 (encode (unit i),0) := by
 apply Prod.ext <;> apply Fin.ext <;>
  simp [splitInput,finProdFinEquiv,encode_unit,Nat.pow_add]

lemma selected_image (q w : ℕ) (v : Vec (Fin (w+1))) (p : Fin (w+1)) (hp : v p=1) (c : Fin q) :
 (permutation q w v p hp (encode (unit (⟨c.val,by rw [Nat.mul_add,Nat.mul_one];have h:=c.isLt;omega⟩:Fin (q*(w+1)))))).val=
 2^(c.val*(w+1))*(encode v).val := by
 change (nativeFiber q w v p hp (splitInput q w _)).val=_
 rw [split_selected,nativeFiber_selected_image,copy_value]

lemma representative_image (q w : ℕ) (v : Vec (Fin (w+1))) (p : Fin (w+1)) (hp : v p=1)
 (c : Fin q) (i : Fin w) :
 (permutation q w v p hp (encode (unit
  (⟨q+(finProdFinEquiv (c,i)).val,by rw [Nat.mul_add,Nat.mul_one];have h:=(finProdFinEquiv (c,i)).isLt;omega⟩:Fin (q*(w+1)))))).val=
 2^(finProdFinEquiv (c,p.succAbove i)).val := by
 change (nativeFiber q w v p hp (splitInput q w _)).val=_
 rw [split_representative,nativeFiber_representative_image,encode_unit]

lemma omitted_succAbove (w : ℕ) (p : Fin (w+1)) (i : Fin w) :
 UniformResidualBasisMachine.omitted p.val (p.succAbove i).val=i.val := by
 by_cases hi:i.val<p.val
 · rw [Fin.succAbove_of_castSucc_lt p i (by exact hi)]
   simp [UniformResidualBasisMachine.omitted,hi]
 · rw [Fin.succAbove_of_le_castSucc p i (by exact Nat.le_of_not_lt hi)]
   simp only [UniformResidualBasisMachine.omitted,Fin.val_succ]
   rw [ite_eq_right (by omega)]
   omega

lemma representative_slot (q w : ℕ) (p : Fin (w+1)) (c : Fin q) (i : Fin w) :
 UniformResidualBasisMachine.repSlot q (w+1) p.val (finProdFinEquiv (c,p.succAbove i)).val=
 q+(finProdFinEquiv (c,i)).val := by
 unfold UniformResidualBasisMachine.repSlot
 have div : (finProdFinEquiv (c,p.succAbove i)).val/(w+1)=c.val := by
  simp [finProdFinEquiv,Nat.add_mul_div_left,Nat.div_eq_of_lt (p.succAbove i).isLt]
 have mod : (finProdFinEquiv (c,p.succAbove i)).val%(w+1)=(p.succAbove i).val := by
  simp [finProdFinEquiv,Nat.mod_eq_of_lt (p.succAbove i).isLt]
 rw [div,mod,omitted_succAbove]
 simp [finProdFinEquiv]
 ring

/-- The actual descriptor bank is the unit-image bank of the concrete native
fiber permutation. No arbitrary address decoder is assumed. -/
theorem unit_image_bank (q w A : ℕ) (v : Vec (Fin (w+1))) (p : Fin (w+1)) (hp : v p=1)
 (s : UniformMachine.State)
 (selected : ∀c,c<q → s.natHeap (A+c)=some (2^(c*(w+1))*(encode v).val))
 (representatives : ∀t,t<q*(w+1) → t%(w+1)≠p.val →
  s.natHeap (A+UniformResidualBasisMachine.repSlot q (w+1) p.val t)=some (2^t)) :
 ∀i:Fin (q*(w+1)),s.natHeap (A+i.val)=some ((permutation q w v p hp (encode (unit i))).val) := by
 intro i
 by_cases low:i.val<q
 · have eqi:i=(⟨i.val,i.isLt⟩:Fin (q*(w+1))) := rfl
   rw [eqi,selected_image q w v p hp (⟨i.val,low⟩:Fin q)]
   exact selected i.val low
 · have h:i.val-q<q*w := by
    have hi:i.val<q*w+q:=by simpa only [Nat.mul_add,Nat.mul_one] using i.isLt
    omega
   let rep:Fin (q*w):=⟨i.val-q,h⟩
   obtain ⟨⟨c,l⟩,hr⟩:=(finProdFinEquiv : Fin q×Fin w≃Fin (q*w)).surjective rep
   have iv:i.val=q+(finProdFinEquiv (c,l)).val := by rw [hr];simp [rep];omega
   have eqi:i=(⟨q+(finProdFinEquiv (c,l)).val,by rw [Nat.mul_add,Nat.mul_one];have hi:=(finProdFinEquiv (c,l)).isLt;omega⟩:Fin (q*(w+1))) := Fin.ext iv
   rw [eqi,representative_image]
   have mod : (finProdFinEquiv (c,p.succAbove l)).val%(w+1)=(p.succAbove l).val := by
    simp [finProdFinEquiv,Nat.mod_eq_of_lt (p.succAbove l).isLt]
   have neq:(p.succAbove l).val≠p.val := by intro eq;exact Fin.succAbove_ne p l (Fin.ext eq)
   have bank:=representatives (finProdFinEquiv (c,p.succAbove l)).val
    (finProdFinEquiv (c,p.succAbove l)).isLt (by rwa [mod])
   rwa [representative_slot] at bank

def image (q w : ℕ) (v : Vec (Fin (w+1))) (p : Fin (w+1)) (hp : v p=1) (i : ℕ) : ℕ :=
 if hi:i<q*(w+1) then (permutation q w v p hp (encode (unit ⟨i,hi⟩))).val else 0

lemma image_small (q w : ℕ) (v : Vec (Fin (w+1))) (p : Fin (w+1)) (hp : v p=1)
 (i : ℕ) (hi:i<q*(w+1)) : image q w v p hp i<2^(q*(w+1)) := by
 simp only [image,dite_eq_left hi]
 exact Fin.isLt _

/-- The concrete physical DFS order, including contiguous q-bit fibers. -/
theorem address_eq_permutation (q w : ℕ) (v : Vec (Fin (w+1))) (p : Fin (w+1)) (hp : v p=1)
 (j : Fin (2^(q*(w+1)))) :
 address (image q w v p hp) (q*(w+1)) 0 j.val=(permutation q w v p hp j).val := by
 have a:=address_of_xor_equiv (permutation q w v p hp) (permutation_zero q w v p hp)
  (permutation_xor q w v p hp) (image q w v p hp)
  (by intro i;simp [image,i.isLt]) (q*(w+1)) 0 j.val (by omega) j.isLt
 simpa using a

end
end ExactFourierCircuits.UniformResidualPermutation

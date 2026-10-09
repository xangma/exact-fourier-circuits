import UniformPhysicalCRTCoordinates
import Mathlib.Data.Fin.Rev

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2, linear CRT index enumeration after (5.5), PDF p.22
(`eq:crt-fourier`), and prefix bound (4.1), PDF p.18.

Mixed-radix carry enumeration is an implementation refinement of the paper's
linear traversal. Initialization, carry visits, frames and instruction counts
have no one-to-one paper lemma; the final caller charges this actual producer.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFastPhysicalCRTArithmetic
open UniformCRTTraversalCycle
open scoped BigOperators
noncomputable section

def reverse {a:ℕ}(r:Fin a→ℕ)(i:Fin a):ℕ:=r i.rev
def digits {a:ℕ}(r:Fin a→ℕ)(p:ℕ)(i:Fin a):ℕ:=decoded (reverse r) p i.rev
def front {a:ℕ}(r:Fin a→ℕ)(t j:ℕ)(i:Fin a):ℕ:=frontDigits (reverse r) t j i.rev
def value {a:ℕ}(r ds:Fin a→ℕ):ℕ:=∑i,place r i.val*ds i
def normal {a:ℕ}(r:Fin a→ℕ)(p:ℕ):ℕ:=value r (digits r p)

lemma reverse_positive {a:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i):∀i,0<reverse r i:=fun i=>hr i.rev
lemma reverse_list {a:ℕ}(r:Fin a→ℕ):List.ofFn (reverse r)=(List.ofFn r).reverse:=by
 apply List.ext_getElem
 · simp
 · intro i h1 h2
   simp only[List.getElem_ofFn,List.getElem_reverse,List.length_ofFn,reverse,Fin.rev]
   congr 1
   apply Fin.ext
   change a-(i+1)=a-1-i
   omega
lemma reverse_product {a:ℕ}(r:Fin a→ℕ):(∏i,reverse r i)=∏i,r i:=by
 simpa only[List.prod_ofFn,List.prod_reverse] using congrArg List.prod (reverse_list r)
lemma place_reverse {a:ℕ}(r:Fin a→ℕ)(i:Fin a):
 place (reverse r) i.rev.val=UniformPhysicalCRTArithmetic.suffix r (i.val+1):=by
 unfold place UniformPhysicalCRTArithmetic.suffix
 rw[reverse_list,List.take_reverse,List.prod_reverse,List.length_ofFn]
 congr 2
 simp only[Fin.val_rev]
 omega
lemma digits_eq {a:ℕ}(r:Fin a→ℕ)(p:ℕ):digits r p=UniformPhysicalCRTArithmetic.digit r p:=by
 funext i
 simp only[digits,decoded,place_reverse,reverse,Fin.rev_rev,UniformPhysicalCRTArithmetic.digit]
lemma normal_eq {a:ℕ}(r:Fin a→ℕ)(p:ℕ):normal r p=UniformPhysicalCRTArithmetic.normal r p:=by
 unfold normal value UniformPhysicalCRTArithmetic.normal encoded
 rw[digits_eq]
lemma digits_zero {a:ℕ}(r:Fin a→ℕ):digits r 0=fun _=>0:=by
 funext i
 simp[digits,decoded]
lemma value_encoded {a:ℕ}(r ds:Fin a→ℕ):value r ds=encoded r ds:=rfl
lemma value_bound {a:ℕ}(r ds:Fin a→ℕ)(hr:∀i,0<r i)(hd:∀i,ds i<r i):value r ds<∏i,r i:=
 encoded_lt r ds hr hd
lemma term_le {a:ℕ}(r ds:Fin a→ℕ)(i:Fin a):place r i.val*ds i≤value r ds:=by
 unfold value
 exact Finset.single_le_sum (fun j _=>Nat.zero_le (place r j.val*ds j)) (Finset.mem_univ i)
lemma value_update {a:ℕ}(r ds:Fin a→ℕ)(i:Fin a)(d:ℕ):
 value r (Function.update ds i d)=value r ds-ds i*place r i.val+d*place r i.val:=by
 have old:=Finset.sum_erase_add Finset.univ (fun j:Fin a=>place r j.val*ds j) (Finset.mem_univ i)
 have updated: value r (Function.update ds i d)=
  (∑j∈Finset.univ.erase i,place r j.val*ds j)+place r i.val*d:=by
  unfold value
  rw[←Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp only[Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw[Function.update_of_ne (Finset.mem_erase.mp hj).1]
 rw[updated]
 unfold value
 rw[←old,Nat.mul_comm (ds i),Nat.add_sub_cancel_right,Nat.mul_comm d]
lemma front_initial {a:ℕ}(r:Fin a→ℕ)(t:ℕ):front r t 0=digits r (t-1):=by
 funext i
 exact congrFun (UniformCRTTraversalCycle.front_initial (reverse r) t) i.rev
lemma front_final {a:ℕ}(r:Fin a→ℕ)(t:ℕ):front r t a=digits r t:=by
 funext i
 exact congrFun (UniformCRTTraversalCycle.front_final (reverse r) t) i.rev
lemma front_bound {a:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i)(t j:ℕ)(i:Fin a):front r t j i<r i:=by
 unfold front frontDigits
 split_ifs
 all_goals simpa only[reverse,Fin.rev_rev] using decoded_bound (reverse r) (reverse_positive r hr) _ i.rev
lemma front_value_bound {a:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i)(t j:ℕ):value r (front r t j)<∏i,r i:=
 value_bound r _ hr (front_bound r hr t j)
lemma front_current {a:ℕ}(r:Fin a→ℕ)(t:ℕ)(j:Fin a):
 front r t j.val j.rev=digits r (t-1) j.rev:=by
 simp[front,frontDigits,digits]
lemma increment_mod (d q:ℕ)(hd:d<q):
 (if d+1<q then d+1 else 0)=(d+1)%q:=by
 by_cases h:d+1<q
 · simp[h,Nat.mod_eq_of_lt h]
 · have e:d+1=q:=by omega
   simp[e]
lemma front_update_mod {a:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i)(t:ℕ)(ht:0<t)(j:Fin a)
 (hd:place (reverse r) j.val∣t):
 Function.update (front r t j.val) j.rev ((digits r (t-1) j.rev+1)%r j.rev)=front r t (j.val+1):=by
 have h:=UniformCRTTraversalCycle.front_update (reverse r) (reverse_positive r hr) t ht j hd
 have hb:=decoded_bound (reverse r) (reverse_positive r hr) (t-1) j
 rw[increment_mod _ _ hb] at h
 funext i
 have hi:=congrFun h i.rev
 by_cases e:i=j.rev
 · subst i
   simpa only[Function.update_self,front,digits,reverse,Fin.rev_rev] using hi
 · have ne:i.rev≠j:=by intro bad;exact e (by simpa only[Fin.rev_rev] using congrArg Fin.rev bad)
   simpa only[Function.update_of_ne e,Function.update_of_ne ne,front] using hi
lemma front_success {a:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i)(t:ℕ)(ht:0<t)(j:Fin a)
 (hd:¬place (reverse r) (j.val+1)∣t):front r t (j.val+1)=digits r t:=by
 funext i
 exact congrFun (UniformCRTTraversalCycle.front_success (reverse r) (reverse_positive r hr) t ht j hd) i.rev
lemma digits_bound {a:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i)(p:ℕ)(i:Fin a):digits r p i<r i:=by
 simpa only[digits,reverse,Fin.rev_rev] using decoded_bound (reverse r) (reverse_positive r hr) p i.rev
lemma normal_bound {a:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i)(p:ℕ):normal r p<∏i,r i:=
 value_bound r _ hr (digits_bound r hr p)
lemma carry_value {a:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i)(t:ℕ)(ht:0<t)(j:Fin a)
 (hd:place (reverse r) j.val∣t):
 value r (front r t (j.val+1))=value r (front r t j.val)-
  digits r (t-1) j.rev*place r j.rev.val+
  ((digits r (t-1) j.rev+1)%r j.rev)*place r j.rev.val:=by
 rw[←front_update_mod r hr t ht j hd,value_update,front_current]
lemma carry_remove_le {a:ℕ}(r:Fin a→ℕ)(t:ℕ)(j:Fin a):
 digits r (t-1) j.rev*place r j.rev.val≤value r (front r t j.val):=by
 have h:=term_le r (front r t j.val) j.rev
 rw[front_current,Nat.mul_comm] at h
 exact h
lemma digits_cycle {a:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i):digits r (∏i,r i)=fun _=>0:=by
 funext i
 change decoded (reverse r) (∏j,r j) i.rev=0
 rw[←reverse_product r]
 exact (next_place_dvd_iff (reverse r) (reverse_positive r hr) (∏j,reverse r j) i.rev
  (place_dvd_all (reverse r) i.rev.val)).1 (place_dvd_all (reverse r) (i.rev.val+1))
end
end ExactFourierCircuits.UniformFastPhysicalCRTArithmetic

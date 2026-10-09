import UniformCRTTraversalCycle
set_option autoImplicit false
namespace ExactFourierCircuits.UniformPhysicalCRTArithmetic
open UniformCRTTraversalCycle
open scoped BigOperators
noncomputable section

def suffix {a:ℕ}(r:Fin a→ℕ)(j:ℕ):ℕ:=((List.ofFn r).drop j).prod
def digit {a:ℕ}(r:Fin a→ℕ)(p:ℕ)(j:Fin a):ℕ:=(p/suffix r (j.val+1))%r j
def normal {a:ℕ}(r:Fin a→ℕ)(p:ℕ):ℕ:=encoded r (digit r p)
def accumulated {a:ℕ}(r:Fin a→ℕ)(p j:ℕ):ℕ:=prefixValue r (digit r p) j
lemma suffix_zero {a:ℕ}(r:Fin a→ℕ):suffix r 0=∏i,r i:=by simp[suffix,List.prod_ofFn]
lemma suffix_all {a:ℕ}(r:Fin a→ℕ):suffix r a=1:=by
 unfold suffix
 rw[List.drop_eq_nil_iff.mpr (by simp),List.prod_nil]
lemma suffix_succ {a:ℕ}(r:Fin a→ℕ)(j:Fin a):suffix r j.val=r j*suffix r (j.val+1):=by
 unfold suffix
 rw[List.drop_eq_getElem_cons (by simp),List.prod_cons]
 simp
lemma suffix_pos {a:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i)(j:ℕ):0<suffix r j:=by
 apply List.prod_pos
 intro v hv
 obtain ⟨i,rfl⟩:=List.mem_ofFn.mp (List.mem_of_mem_drop hv)
 exact hr i
lemma split_product {a:ℕ}(r:Fin a→ℕ)(j:ℕ):place r j*suffix r j=∏i,r i:=by
 simpa only[place,suffix,List.prod_ofFn] using List.prod_take_mul_prod_drop (List.ofFn r) j
lemma place_le {a:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i)(j:ℕ):place r j≤∏i,r i:=by
 have h:=suffix_pos r hr j
 have e:=split_product r j
 nlinarith
lemma suffix_le {a:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i)(j:ℕ):suffix r j≤∏i,r i:=by
 have h:=place_pos r hr j
 have e:=split_product r j
 nlinarith
lemma divisor_step {a:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i)(j:Fin a):
 suffix r j.val/r j=suffix r (j.val+1):=by
 rw[suffix_succ,Nat.mul_div_cancel_left _ (hr j)]
lemma digit_lt {a:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i)(p:ℕ)(j:Fin a):digit r p j<r j:=Nat.mod_lt _ (hr j)
lemma prefix_zero {a:ℕ}(r:Fin a→ℕ)(p:ℕ):accumulated r p 0=0:=UniformCRTTraversalCycle.prefix_zero _ _
lemma prefix_succ {a:ℕ}(r:Fin a→ℕ)(p:ℕ)(j:Fin a):
 accumulated r p (j.val+1)=accumulated r p j.val+place r j.val*digit r p j:=UniformCRTTraversalCycle.prefix_succ _ _ _
lemma prefix_all {a:ℕ}(r:Fin a→ℕ)(p:ℕ):accumulated r p a=normal r p:=UniformCRTTraversalCycle.prefix_all _ _
lemma prefix_lt {a:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i)(p j:ℕ)(hj:j≤a):
 accumulated r p j<place r j:=UniformCRTTraversalCycle.prefix_lt r _ hr (digit_lt r hr p) j hj
lemma normal_lt {a:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i)(p:ℕ):normal r p<∏i,r i:=encoded_lt r _ hr (digit_lt r hr p)
lemma product_digit_le {a:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i)(p:ℕ)(j:Fin a):
 place r j.val*digit r p j≤∏i,r i:=by
 have hd:=digit_lt r hr p j
 have h:=place_le r hr (j.val+1)
 rw[place_succ] at h
 nlinarith
end
end ExactFourierCircuits.UniformPhysicalCRTArithmetic

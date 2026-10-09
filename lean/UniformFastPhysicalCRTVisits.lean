import UniformFastPhysicalCRTArithmetic

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
open UniformCRTTraversalCycle UniformCRTTraversalMachine
open scoped BigOperators
noncomputable section

lemma totalVisits_mono {a:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i){k l:ℕ}(h:k≤l):
 totalVisits r k≤totalVisits r l:=by
 unfold totalVisits
 apply Finset.sum_le_sum
 intro i _
 rw[multiples_eq _ (place_pos r hr _),multiples_eq _ (place_pos r hr _)]
 exact Nat.div_le_div_right h
lemma two_valid (rs:List ℕ)(h:∀q∈rs,2≤q):CarryRadices rs:=by
 constructor
 · intro q hq;have hb:=h q hq;omega
 · intro i hi
   exact h _ (List.getElem_mem (by omega))
lemma reverse_valid {a:ℕ}(r:Fin a→ℕ)(hr:∀i,2≤r i):CarryRadices (List.ofFn (reverse r)):=by
 apply two_valid
 intro q hq
 obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
 exact hr i.rev
/-- The actual physical odometer visits the rightmost axis first. All selected
positive-length radices are at least two, so the full finite count is <2V. -/
/- Paper stage: §4.1 (4.1), PDF p.18, used by §5.2, PDF p.22: all selected positive-length radices >=2 give fewer than 2L odometer visits. -/
lemma reverse_totalVisits {a:ℕ}(r:Fin a→ℕ)(hr:∀i,2≤r i):
 totalVisits (reverse r) (∏i,r i)<2*(∏i,r i):=by
 have positive:∀i,0<r i:=fun i=>lt_of_lt_of_le (by decide) (hr i)
 have h:=carryVisits_bound (List.ofFn (reverse r)) (reverse_valid r hr)
 rw[←totalVisits_cycle (reverse r) (reverse_positive r positive),reverse_product] at h
 simpa only[List.prod_ofFn,reverse_product] using h
lemma reverse_prefixVisits {a:ℕ}(r:Fin a→ℕ)(hr:∀i,2≤r i)(k:ℕ)(hk:k≤∏i,r i):
 totalVisits (reverse r) k<2*(∏i,r i):=
 lt_of_le_of_lt (totalVisits_mono _ (reverse_positive r (fun i=>lt_of_lt_of_le (by decide) (hr i))) hk)
  (reverse_totalVisits r hr)
end
end ExactFourierCircuits.UniformFastPhysicalCRTArithmetic

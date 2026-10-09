import UniformJointCacheAllocation
import UniformLocalCacheTiming
import UniformTransposeDescriptorMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformJointCacheTime
open UniformJointAllocation UniformJointCacheExtent UniformWorkspacePlanner
open UniformLocalRectangleDescriptors UniformLocalCacheTreeMachine UniformLocalCacheTiming
noncomputable section

lemma sum_squares (a b:ℕ):a^2+b^2≤ (a+b)^2:=by
 nlinarith only[Nat.zero_le (a*b)]

lemma leaf_records_bound (v o K:ℕ):(UniformTransposeDescriptorMachine.leafRecords v o K).length≤  v^2:=by
 rw[UniformTransposeDescriptorMachine.leafRecords_length]
 have division:=Nat.div_le_self (v*(v-1)) 2
 by_cases zero:v=0
 · subst v;simp
 · have sub:v-1+1=v:=Nat.sub_add_cancel (by omega)
   nlinarith
/-- Actual four-word leaf descriptors, counted over the real balanced plan. -/
def leafOperations:{r:ℕ}→UniformBalancedToeplitz.Plan r→ℕ
 | _,.direct v _=>(UniformTransposeDescriptorMachine.leafRecords v 0 0).length
 | _,.split _ _ _ L R=>leafOperations L+leafOperations R
lemma leaf_operations_bound {r:ℕ} (P:UniformBalancedToeplitz.Plan r):leafOperations P≤  r^2:=by
 induction P with
 | direct v _=>exact leaf_records_bound v 0 0
 | split v _ _ L R ihL ihR=>
  change leafOperations L+leafOperations R≤  v^2
  have sub:v/2+(v-v/2)=v:=Nat.add_sub_of_le (Nat.div_le_self _ _)
  have squares:=sum_squares (v/2) (v-v/2)
  rw[sub] at squares
  nlinarith only[ihL,ihR,squares]
lemma full_slots_bound (r:ℕ) (P:UniformBalancedToeplitz.Plan r):
 ((UniformLocalPreparationDAG.requests P (le_refl r)).map (fun q=>slotCount q.k)).sum+
  2*leafOperations P≤  capacity r:=by
 have slots:=actual_request_slots r P
 have leaves:=leaf_operations_bound P
 omega

lemma sum_scale (C:ℕ) (ls:List ℕ):(ls.map (fun k=>C*k)).sum=C*ls.sum:=by
 induction ls with
 | nil=>simp
 | cons a ls ih=>simp only[List.map_cons,List.sum_cons,ih];ring
lemma rectangle_slot_duration (q:Row):rectangleDuration q=28*slotCount (exponent q.a q.e):=by
 rw[slotCount_formula]
 unfold rectangleDuration
 ring
lemma correction_duration {r N:ℕ} (hn:2≤ r) (hv:0<selected r) (hN:r≤ N):
 rectanglesDuration (rows r 0 (selected r))=
 28*((UniformBalancedToeplitz.pairs r).map
  (fun q=>slotCount (UniformLocalPreparationDAG.pairRequest hn hv hN q).k)).sum:=by
 unfold rectanglesDuration
 rw[rows_pairs]
 have eq:((UniformBalancedToeplitz.pairs r).map
  (fun q=>rectangleDuration (row r 0 (selected r) q.1.val q.2.val)))=
  (((UniformBalancedToeplitz.pairs r).map
   (fun q=>slotCount (UniformLocalPreparationDAG.pairRequest hn hv hN q).k)).map (fun k=>28*k)):=by
  rw[List.map_map]
  apply List.map_congr_left
  intro q _
  rw[rectangle_slot_duration]
  rfl
 rw[List.map_map]
 change ((UniformBalancedToeplitz.pairs r).map
  (fun q=>rectangleDuration (row r 0 (selected r) q.1.val q.2.val))).sum=_
 rw[eq,sum_scale]

/-- A semantic word bound for the real fused schedule: parallel children cost
at most their sum, while each actual rectangle has exactly28 ticks per slot. -/
lemma plan_duration_bound {r N:ℕ} (P:UniformBalancedToeplitz.Plan r) (hN:r≤ N):
 planDuration P≤  14*r^2+28*((UniformLocalPreparationDAG.requests P hN).map (fun q=>slotCount q.k)).sum:=by
 induction P generalizing N with
 | direct v _=>
  simp only[planDuration,directDuration,UniformLocalPreparationDAG.requests,List.map_nil,List.sum_nil,
   Nat.mul_zero,Nat.add_zero]
  by_cases zero:v=0
  · subst v;simp
  · have sub:v-1+1=v:=Nat.sub_add_cancel (by omega)
    nlinarith
 | split v hn hv L R ihL ihR=>
  have sub:v/2+(v-v/2)=v:=Nat.add_sub_of_le (Nat.div_le_self _ _)
  have left:=ihL (N:=N) (by omega)
  have right:=ihR (N:=N) (by omega)
  have parallel:max (planDuration L) (planDuration R)≤  planDuration L+planDuration R:=by omega
  simp only[planDuration,UniformLocalPreparationDAG.requests,List.map_append,List.sum_append,List.map_map,Function.comp_def]
  rw[correction_duration hn hv hN]
  have squares:=sum_squares (v/2) (v-v/2)
  rw[sub] at squares
  nlinarith only[left,right,parallel,squares]

lemma duration_word_bound (c:Constants) (n r:ℕ) (P:UniformBalancedToeplitz.Plan r) (hr:r≤ 4*n):
 planDuration P≤  slab c n:=by
 have schedule:=plan_duration_bound P (le_refl r)
 have requests:=actual_request_slots r P
 have r2:r^2≤ 16*(n+2)^2:=by
  have h:=Nat.pow_le_pow_left (show r≤ 4*(n+2) by omega) 2
  convert h using 1;ring
 have slots:=slot_bound hr
 have cap:capacity r≤ 96000*(n+2)^3:=by
  have h:=Nat.mul_le_mul r2 slots
  unfold capacity
  convert h using 1;ring
 have small:planDuration P≤ 3000000*(n+2)^4:=by
  have p2:(n+2)^2≤ (n+2)^4:=Nat.pow_le_pow_right (by omega:1≤ n+2) (by decide:2≤ 4)
  have p3:(n+2)^3≤ (n+2)^4:=Nat.pow_le_pow_right (by omega:1≤ n+2) (by decide:3≤ 4)
  nlinarith only[schedule,requests,r2,cap,p2,p3]
 have big:3000000≤ 100000*(fixed c+1):=by have:=fixed_large c;omega
 exact small.trans ((Nat.mul_le_mul_right ((n+2)^4) big).trans
  (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega:1≤ n+2) (by decide:4≤ 19))))

/-- The actual symbolic forest timestamps fit the same ordinary word slab.
A charged physical duration/start printer remains a distinct execution seam. -/
theorem timed_word_bound (c:Constants) (n r o:ℕ) (P:UniformBalancedToeplitz.Plan r)
 (hr:r≤ 4*n) (e:TimedEvent) (he:e∈treeTimed 0 (ofPlan P o)):
 e.start≤  slab c n ∧e.stop≤  slab c n:=by
 have ends:=(timed_bounds (ofPlan P o) 0 e he).2
 rw[ofPlan_duration,Nat.zero_add] at ends
 have final:=ends.trans (duration_word_bound c n r P hr)
 unfold TimedEvent.stop at final ⊢
 omega

end
end ExactFourierCircuits.UniformJointCacheTime

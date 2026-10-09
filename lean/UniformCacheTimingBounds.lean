import UniformCacheTimingEvents
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingBounds
open UniformLocalCacheTreeMachine UniformLocalCacheTreeExecution UniformLocalCacheTreeCoverage
open UniformLocalCacheTiming UniformCacheTimingWalk UniformCacheTimingReference UniformCacheTimingBottomUp
open UniformCacheTimingMetadata UniformBalancedToeplitz UniformWorkspacePlanner

lemma rectanglesDuration_append (xs ys : List UniformLocalRectangleDescriptors.Row) :
 rectanglesDuration (xs++ys)=rectanglesDuration xs+rectanglesDuration ys := by
 simp only [rectanglesDuration,List.map_append,List.sum_append]
lemma requestPrefix_le (q : Visit) (j : ℕ) : requestPrefix q j ≤ correction q := by
 have h:=rectanglesDuration_append ((currentRows q.task).take j) ((currentRows q.task).drop j)
 rw [List.take_append_drop] at h
 change rectanglesDuration ((currentRows q.task).take j) ≤ rectanglesDuration (currentRows q.task)
 omega
lemma correction_le (q : Visit) : correction q ≤ taskDuration q.task := by
 unfold taskDuration
 rw [plan]
 split
 · rename_i h
   simp only [correction,currentRows,h,ite_true,rectanglesDuration,List.map_nil,List.sum_nil]
   exact Nat.zero_le _
 · rename_i h
   simp only [ofPlan,treeDuration,correction,currentRows,h,ite_false]
   omega
lemma requestStart_le (q : Visit) (j : ℕ) : requestStart q j ≤ taskDuration q.task := by
 have a:=requestPrefix_le q j
 have b:=correction_le q
 unfold requestStart
 omega

lemma numbered_duration_le {v : ℕ} (P : Plan v) (hp : Canonical P)
 (o k c parent side : ℕ) (q : Visit) (hq:q∈numbered P o k c parent side) :
 taskDuration q.task ≤ treeDuration (ofPlan P o) := by
 induction P generalizing o k c parent side with
 | direct v cap =>
  simp only [numbered,List.mem_singleton] at hq
  subst q
  rw [taskDuration_ofPlan (.direct v cap) hp o parent side]
 | split v hn hv L R ihL ihR =>
  let lc:=c+7*UniformLocalRectangleDescriptors.emittedCount v
  let ls:=numbered L o (k+1) lc k 0
  let rs:=numbered R (o+v/2) (k+1+ls.length) (lc+7*visitSum ls) k 1
  change q∈⟨⟨v,o,parent,side⟩,c⟩::(ls++rs) at hq
  simp only [List.mem_cons,List.mem_append] at hq
  rcases hq with hq|hq|hq
  · subst q
    rw [taskDuration_ofPlan (.split v hn hv L R) hp o parent side]
  · have h:=ihL hp.2.1 o (k+1) lc k 0 hq
    have mx:=le_max_left (treeDuration (ofPlan L o)) (treeDuration (ofPlan R (o+v/2)))
    change taskDuration q.task ≤ max _ _+_
    omega
  · have h:=ihR hp.2.2 (o+v/2) (k+1+ls.length) (lc+7*visitSum ls) k 1 hq
    have mx:=le_max_right (treeDuration (ofPlan L o)) (treeDuration (ofPlan R (o+v/2)))
    change taskDuration q.task ≤ max _ _+_
    omega

lemma root_duration_le (v o R i : ℕ)
 (hi:i<(walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1.length) :
 taskDuration (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1[i].task ≤ planDuration (plan v) := by
 let q:=(walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1[i]
 have mem:q∈numbered (plan v) o 0 R 0 0:=by simpa only [q,root_walk_numbered] using List.getElem_mem hi
 simpa only [ofPlan_duration] using numbered_duration_le (plan v) (plan_canonical v) o 0 R 0 0 _ mem

lemma bottomUpFrom_high (k : ℕ) (visits : List Visit) (d : ℕ→ℕ) (j : ℕ)
 (high:k+visits.length ≤ j) (parents:∀q∈visits,q.task.parent<j) :
 bottomUpFrom k visits d j=d j := by
 induction visits generalizing k with
 | nil => rfl
 | cons q qs ih =>
  rw [bottomUpFrom,bottomStep_other k q _ j (by simp only [List.length_cons] at high;omega)
   (Or.inr (by have:=parents q (by simp);omega))]
  exact ih (k+1) (by simp only [List.length_cons] at high;omega)
   (fun r hr=>parents r (by simp [hr]))

def ParentsLE (visits : List Visit) : Prop :=
 ∀ (i : ℕ) (hi : i < visits.length), visits[i].task.parent ≤ i
lemma root_parentsLE (v o R : ℕ) : ParentsLE (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1 := by
 intro i hi
 by_cases zero:i=0
 · subst i
   simp only [walk,List.append_nil,List.getElem_cons_zero]
   omega
 · exact Nat.le_of_lt (root_parentBefore v o R i hi (by omega))

/-- Earlier-node processing cannot change an already completed duration cell. -/
lemma suffix_completed (visits : List Visit) (parents : ParentsLE visits)
 (k j : ℕ) (hk:k ≤ visits.length) (hj:k ≤ j) :
 processedSuffix visits k j=bottomUp visits j := by
 have earlier : ∀q∈visits.take k,q.task.parent<j := by
  intro q hq
  obtain ⟨i,hi,eq⟩:=List.mem_iff_getElem.mp hq
  have ik:i<k:=by simp only [List.length_take] at hi;omega
  have il:i<visits.length:=by simp only [List.length_take] at hi;omega
  have h:=parents i il
  have qeq : q=visits[i]:=by simpa only [List.getElem_take] using eq.symm
  rw [qeq]
  omega
 have same:=bottomUpFrom_high 0 (visits.take k) (processedSuffix visits k) j
  (by simp only [List.length_take,Nat.zero_add];omega) earlier
 have split:=congrFun (bottomUpFrom_append 0 (visits.take k) (visits.drop k) (fun _=>0)) j
 simp only [List.take_append_drop,Nat.zero_add,List.length_take,Nat.min_eq_left hk] at split
 exact same.symm.trans split.symm

lemma update_bounded (d : ℕ→ℕ) (k value M : ℕ)
 (bound:∀j,d j ≤ M) (vb:value ≤ M) : ∀j,Function.update d k value j ≤ M := by
 intro j
 by_cases eq:j=k
 · simp only [Function.update_apply,eq,ite_true];exact vb
 · simp only [Function.update_apply,eq,ite_false];exact bound j
lemma bottomStep_bounded (k : ℕ) (q : Visit) (d : ℕ→ℕ) (M : ℕ)
 (bound:∀j,d j ≤ M)
 (vb:(if q.task.width<2 ∨ selected q.task.width=0 then directDuration q.task.width else d k+correction q) ≤ M) :
 ∀j,bottomStep k q d j ≤ M := by
 let value:=if q.task.width<2 ∨ selected q.task.width=0 then directDuration q.task.width else d k+correction q
 have next:=update_bounded d k value M bound vb
 intro j
 change (if k=0 then Function.update d k value else
  Function.update (Function.update d k value) q.task.parent (max (Function.update d k value q.task.parent) value)) j ≤ M
 split
 · exact next j
 · exact update_bounded _ _ _ M next (max_le (next q.task.parent) vb) j

lemma bottomStep_self_any (k : ℕ) (q : Visit) (d : ℕ→ℕ) :
 bottomStep k q d k=
 if q.task.width<2 ∨ selected q.task.width=0 then directDuration q.task.width else d k+correction q := by
 unfold bottomStep
 split_ifs with leaf zero
 all_goals simp only [Function.update_apply]
 all_goals split_ifs <;> omega

/-- All intermediate reverse-pass words are bounded by the final schedule
length, including unfinished parent maxima. -/
lemma processedSuffix_bound (visits : List Visit) (parents : ParentsLE visits) (M : ℕ)
 (final:∀i (_hi:i<visits.length),bottomUp visits i ≤ M)
 (k : ℕ) (hk:k ≤ visits.length) : ∀j,processedSuffix visits k j ≤ M := by
 have reverse : ∀rem k,k+rem=visits.length → ∀j,processedSuffix visits k j ≤ M := by
  intro rem
  induction rem with
  | zero =>
   intro k eq j
   have ke:k=visits.length:=by omega
   subst k
   rw [processedSuffix_end]
   exact Nat.zero_le _
  | succ rem ih =>
   intro k eq j
   have ki:k<visits.length:=by omega
   have rest:=ih (k+1) (by omega)
   have self:=bottomStep_self_any k visits[k] (processedSuffix visits (k+1))
   have done:=suffix_completed visits parents k k (by omega) (le_refl k)
   rw [processedSuffix_step visits k ki] at done
   have vb:=final k ki
   rw [←done,self] at vb
   rw [processedSuffix_step visits k ki]
   exact bottomStep_bounded k visits[k] _ M rest vb j
 exact reverse (visits.length-k) k (by omega)

lemma root_processedSuffix_bound (v o R k : ℕ)
 (hk:k ≤ (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1.length) :
 ∀j,processedSuffix (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1 k j ≤ planDuration (plan v) := by
 apply processedSuffix_bound _ (root_parentsLE v o R) _ _ k hk
 intro i hi
 rw [root_bottomUp v o R i hi]
 exact root_duration_le v o R i hi

lemma visitSum_append (xs ys : List Visit) : visitSum (xs++ys)=visitSum xs+visitSum ys := by
 simp only [visitSum,List.map_append,List.sum_append]
lemma visitSum_take_le (visits : List Visit) (i : ℕ) : visitSum (visits.take i) ≤ visitSum visits := by
 have h:=visitSum_append (visits.take i) (visits.drop i)
 rw [List.take_append_drop] at h
 omega
lemma visitSum_take_mono (visits : List Visit) (i j : ℕ) (h:i ≤ j) :
 visitSum (visits.take i) ≤ visitSum (visits.take j) := by
 simpa only [List.take_take,Nat.min_eq_left h] using visitSum_take_le (visits.take j) i
lemma visitSum_take_step (visits : List Visit) (i : ℕ) (hi:i<visits.length) :
 visitSum (visits.take (i+1))=visitSum (visits.take i)+UniformLocalRectangleDescriptors.emittedCount visits[i].task.width := by
 rw [List.take_succ_eq_append_getElem hi,visitSum_append]
 simp only [visitSum,List.map_singleton,List.sum_singleton]
lemma visitSum_request_before (visits : List Visit) (i j : ℕ) (hi:i<visits.length) (h:i<j) :
 visitSum (visits.take i)+UniformLocalRectangleDescriptors.emittedCount visits[i].task.width ≤ visitSum (visits.take j) := by
 rw [←visitSum_take_step visits i hi]
 exact visitSum_take_mono visits (i+1) j (by omega)
lemma visitSum_request_end (visits : List Visit) (i : ℕ) (hi:i<visits.length) :
 visitSum (visits.take i)+UniformLocalRectangleDescriptors.emittedCount visits[i].task.width ≤ visitSum visits := by
 rw [←visitSum_take_step visits i hi]
 exact visitSum_take_le visits (i+1)

end ExactFourierCircuits.UniformCacheTimingBounds

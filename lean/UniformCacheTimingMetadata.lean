import UniformCacheTimingWalk
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingMetadata
open UniformLocalCacheTreeMachine UniformLocalCacheTreeExecution UniformCacheTimingWalk
open UniformLocalRectangleDescriptors (emittedCount)

/-- The real DFS gives every non-root child a strictly earlier parent ID. -/
def ParentBefore (visits : List Visit) : Prop :=
 ∀ (i : ℕ) (hi : i < visits.length), 0 < i → visits[i].task.parent < i

lemma walk_parents (fuel k c : ℕ) (tasks : List Task)
 (parents : ∀t∈tasks,t.parent<k) :
 ∀ i (hi:i<(walk fuel k c tasks).1.length),
  (walk fuel k c tasks).1[i].task.parent<k+i := by
 induction fuel generalizing k c tasks with
 | zero => simp [walk]
 | succ fuel ih =>
  cases tasks with
  | nil => simp [walk]
  | cons t ts =>
   have next : ∀u∈children t k++ts,u.parent<k+1 := by
    intro u hu
    rcases List.mem_append.mp hu with hu|hu
    · have h:=children_bound t k u hu;omega
    · have h:=parents u (by simp [hu]);omega
   intro i hi
   cases i with
   | zero => simpa only [walk,List.getElem_cons_zero,Nat.add_zero] using parents t (by simp)
   | succ i =>
    have ht : i<(walk fuel (k+1) (c+7*emittedCount t.width) (children t k++ts)).1.length := by
     simpa only [walk,List.length_cons,Nat.succ_lt_succ_iff] using hi
    have h:=ih (k+1) (c+7*emittedCount t.width) (children t k++ts) next i ht
    simpa only [walk,List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

lemma root_parentBefore (v o R : ℕ) :
 ParentBefore (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1 := by
 intro i hi positive
 obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega:i≠0)
 have parents : ∀u∈children ⟨v,o,0,0⟩ 0,u.parent<1 := by
  intro u hu
  have h:=children_bound ⟨v,o,0,0⟩ 0 u hu;omega
 have ht : j<(walk (2*v) 1 (R+7*emittedCount v) (children ⟨v,o,0,0⟩ 0)).1.length := by
  simpa only [walk,List.append_nil,List.length_cons,Nat.succ_lt_succ_iff] using hi
 have h:=walk_parents (2*v) 1 (R+7*emittedCount v) (children ⟨v,o,0,0⟩ 0) parents j ht
 simpa only [walk,List.append_nil,List.getElem_cons_succ,Nat.add_comm] using h

/-- Every printed request pointer is the real traversal's prior rectangle
count; ragged/empty nodes contribute their exact emittedCount. -/
lemma walk_rectangle_prefix (fuel k c : ℕ) (tasks : List Task) :
 ∀ i (hi:i<(walk fuel k c tasks).1.length),
 (walk fuel k c tasks).1[i].rectangleBase=
  c+7*visitSum ((walk fuel k c tasks).1.take i) := by
 induction fuel generalizing k c tasks with
 | zero => simp [walk]
 | succ fuel ih =>
  cases tasks with
  | nil => simp [walk]
  | cons t ts =>
   intro i hi
   cases i with
   | zero => simp [walk,visitSum]
   | succ i =>
    have ht : i<(walk fuel (k+1) (c+7*emittedCount t.width) (children t k++ts)).1.length := by
     simpa only [walk,List.length_cons,Nat.succ_lt_succ_iff] using hi
    have h:=ih (k+1) (c+7*emittedCount t.width) (children t k++ts) i ht
    simpa only [walk,List.getElem_cons_succ,List.take_succ_cons,visitSum,List.map_cons,
      List.sum_cons,Nat.mul_add,Nat.add_assoc] using h

lemma root_request_ordinal (v o R i : ℕ)
 (hi:i<(walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1.length) :
 ((walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1[i].rectangleBase-R)/7=
 visitSum ((walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1.take i) := by
 rw [walk_rectangle_prefix]
 simp

end ExactFourierCircuits.UniformCacheTimingMetadata

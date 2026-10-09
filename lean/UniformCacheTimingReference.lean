import UniformCacheTimingWalk
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingReference
open UniformLocalCacheTreeMachine UniformLocalCacheTreeExecution
open UniformLocalCacheTreeCoverage UniformLocalCacheTiming UniformCacheTimingWalk
open UniformBalancedToeplitz UniformWorkspacePlanner

/-- Semantic duration of the exact measured subtree rooted at this physical task. -/
def taskDuration (t : Task) : ℕ := treeDuration (ofPlan (plan t.width) t.offset)
def correction (q : Visit) : ℕ := rectanglesDuration (currentRows q.task)
def requestPrefix (q : Visit) (j : ℕ) : ℕ :=
 rectanglesDuration ((currentRows q.task).take j)
def requestStart (q : Visit) (j : ℕ) : ℕ :=
 taskDuration q.task-correction q+requestPrefix q j

lemma canonical_eq_plan {v : ℕ} (P : Plan v) (hp : Canonical P) : P=plan v := by
 induction P with
 | direct v cap =>
  rw [plan]
  split
  · rfl
  · rename_i h;exact False.elim (h hp)
 | split v hn hv L R ihL ihR =>
  rw [plan]
  split
  · rename_i h;exact False.elim (hp.1 h)
  · rw [←ihL hp.2.1,←ihR hp.2.2]

lemma taskDuration_ofPlan {v : ℕ} (P : Plan v) (hp : Canonical P)
 (o parent side : ℕ) : taskDuration ⟨v,o,parent,side⟩=treeDuration (ofPlan P o) := by
 rw [canonical_eq_plan P hp]
 rfl

/-- Exact pure reference for the literal reverse-node pass. Its accumulator at
an unfinished parent is the maximum of children already completed. -/
def bottomStep (k : ℕ) (q : Visit) (d : ℕ→ℕ) : ℕ→ℕ :=
 let value := if q.task.width<2 ∨ selected q.task.width=0 then directDuration q.task.width
   else d k+correction q
 let next := Function.update d k value
 if k=0 then next else Function.update next q.task.parent (max (next q.task.parent) value)

def bottomUpFrom : ℕ→List Visit→(ℕ→ℕ)→(ℕ→ℕ)
 | _,[],d => d
 | k,q::qs,d => bottomStep k q (bottomUpFrom (k+1) qs d)
def bottomUp (visits : List Visit) : ℕ→ℕ := bottomUpFrom 0 visits (fun _=>0)
def processedSuffix (visits : List Visit) (k : ℕ) : ℕ→ℕ :=
 bottomUpFrom k (visits.drop k) (fun _=>0)

lemma bottomUpFrom_append (k : ℕ) (xs ys : List Visit) (d : ℕ→ℕ) :
 bottomUpFrom k (xs++ys) d=bottomUpFrom k xs (bottomUpFrom (k+xs.length) ys d) := by
 induction xs generalizing k with
 | nil => rfl
 | cons q qs ih =>
  simp only [bottomUpFrom,List.cons_append,List.length_cons,ih]
  simp only [Nat.add_comm,Nat.add_left_comm]

lemma processedSuffix_step (visits : List Visit) (k : ℕ) (hk : k<visits.length) :
 processedSuffix visits k=bottomStep k visits[k] (processedSuffix visits (k+1)) := by
 unfold processedSuffix
 rw [List.drop_eq_getElem_cons hk]
 rfl
lemma processedSuffix_end (visits : List Visit) : processedSuffix visits visits.length=(fun _=>0) := by
 simp [processedSuffix,bottomUpFrom]
lemma processedSuffix_zero (visits : List Visit) : processedSuffix visits 0=bottomUp visits := by
 simp [processedSuffix,bottomUp]

lemma bottomStep_self (k : ℕ) (q : Visit) (d : ℕ→ℕ)
 (_parent : k=0 ∨ q.task.parent<k) :
 bottomStep k q d k=
 if q.task.width<2 ∨ selected q.task.width=0 then directDuration q.task.width
 else d k+correction q := by
 unfold bottomStep
 split_ifs with leaf zero
 all_goals simp only [Function.update_apply]
 all_goals split_ifs <;> omega

lemma bottomStep_other (k : ℕ) (q : Visit) (d : ℕ→ℕ) (j : ℕ)
 (hk : j≠k) (hp : k=0 ∨ j≠q.task.parent) : bottomStep k q d j=d j := by
 unfold bottomStep
 split_ifs with leaf zero
 all_goals simp only [Function.update_apply]
 all_goals split_ifs <;> omega

end ExactFourierCircuits.UniformCacheTimingReference

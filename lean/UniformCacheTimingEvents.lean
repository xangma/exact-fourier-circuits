import UniformCacheTimingBottomUp
import UniformCacheTimingMetadata
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingEvents
open UniformLocalCacheTreeMachine UniformLocalCacheTreeExecution UniformLocalCacheTreeCoverage
open UniformLocalCacheTiming UniformCacheTimingWalk UniformCacheTimingReference UniformCacheTimingBottomUp
open UniformBalancedToeplitz UniformWorkspacePlanner

/-- Cache records remain in actual preparation order. These timestamps recover
the genuine parallel-child/postorder execution schedule. -/
def nodeEvents (start : ℕ) (t : Task) : List TimedEvent :=
 if t.width<2 ∨ selected t.width=0 then [⟨start,.direct t.width t.offset⟩]
 else sequenceRows (start+(taskDuration t-rectanglesDuration (currentRows t))) (currentRows t)
def events (start : ℕ) (visits : List Visit) : List TimedEvent :=
 visits.flatMap fun q=>nodeEvents start q.task

lemma nodeEvents_split (v o parent side start : ℕ) (hn : 2≤v) (hv : 0<selected v) :
 nodeEvents start ⟨v,o,parent,side⟩=
 sequenceRows (start+max (treeDuration (ofPlan (plan (v/2)) o))
  (treeDuration (ofPlan (plan (v-v/2)) (o+v/2))))
  (UniformLocalRectangleDescriptors.rows v o (selected v)) := by
 have active : ¬(v<2 ∨ selected v=0):=by omega
 unfold nodeEvents taskDuration
 simp only [active,ite_false,currentRows]
 rw [plan]
 simp only [dite_eq_right active,ofPlan,treeDuration,Nat.add_sub_cancel_right]

/-- Every actual preparation record occurs at exactly its timed event, even
though preparation visits a parent before its parallel children. -/
lemma numbered_events {v : ℕ} (P : Plan v) (hp : Canonical P)
 (o k c parent side start : ℕ) :
 (events start (numbered P o k c parent side)).Perm (treeTimed start (ofPlan P o)) := by
 induction P generalizing o k c parent side start with
 | direct v cap =>
  have leaf : v<2 ∨ selected v=0:=hp
  simp only [numbered,events,List.flatMap_cons,List.flatMap_nil,List.append_nil,
   nodeEvents,leaf,ite_true,ofPlan,treeTimed]
  exact List.Perm.refl _
 | split v hn hv L R ihL ihR =>
  let lc:=c+7*UniformLocalRectangleDescriptors.emittedCount v
  let ls:=numbered L o (k+1) lc k 0
  let rs:=numbered R (o+v/2) (k+1+ls.length) (lc+7*visitSum ls) k 1
  have left:=ihL hp.2.1 o (k+1) lc k 0 start
  have right:=ihR hp.2.2 (o+v/2) (k+1+ls.length) (lc+7*visitSum ls) k 1 start
  have shape : numbered (.split v hn hv L R) o k c parent side=
    ⟨⟨v,o,parent,side⟩,c⟩::(ls++rs):=rfl
  rw [shape]
  simp only [events,List.flatMap_cons,List.flatMap_append]
  change (nodeEvents start ⟨v,o,parent,side⟩++(events start ls++events start rs)).Perm _
  rw [nodeEvents_split v o parent side start hn hv,
   ←canonical_eq_plan L hp.2.1,←canonical_eq_plan R hp.2.2]
  change (sequenceRows _ _++(events start ls++events start rs)).Perm
   ((treeTimed start (ofPlan L o)++treeTimed start (ofPlan R (o+v/2)))++sequenceRows _ _)
  exact ((List.Perm.refl _).append (left.append right)).trans List.perm_append_comm

lemma root_events (v o R start : ℕ) :
 (events start (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1).Perm
 (treeTimed start (ofPlan (plan v) o)) := by
 rw [root_walk_numbered]
 exact numbered_events (plan v) (plan_canonical v) o 0 R 0 0 start

/-- Exact per-request start from the sequential rectangle prefix. -/
lemma sequenceRows_index (start : ℕ) (rows : List UniformLocalRectangleDescriptors.Row)
 (j : ℕ) (hj : j<rows.length) :
 (sequenceRows start rows)[j]'(by rw [sequenceRows_length];exact hj)=
 ⟨start+rectanglesDuration (rows.take j),.rectangle rows[j]⟩ := by
 induction rows generalizing start j with
 | nil => simp at hj
 | cons q qs ih =>
  cases j with
  | zero => simp [sequenceRows,rectanglesDuration]
  | succ j =>
   have h:j<qs.length:=by simpa using hj
   simp only [sequenceRows,List.getElem_cons_succ,List.take_succ_cons]
   rw [ih (start+rectangleDuration q) j h]
   simp only [rectanglesDuration,List.map_cons,List.sum_cons]
   congr 1;omega

lemma requestStart_index (q : Visit) (j : ℕ) (hj : j<(currentRows q.task).length) :
 (sequenceRows (taskDuration q.task-correction q) (currentRows q.task))[j]'
   (by rw [sequenceRows_length];exact hj)=
 ⟨requestStart q j,.rectangle (currentRows q.task)[j]⟩ := by
 rw [sequenceRows_index]
 rfl

/-- Replacing the physical reverse-fold duration in the actual row formula
recovers the exact request start, with no supplied time-bank hypothesis. -/
lemma root_requestStart (v o R i j : ℕ)
 (hi : i<(walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1.length) :
 bottomUp (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1 i-
 correction (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1[i]+
 requestPrefix (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1[i] j=
 requestStart (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1[i] j := by
 rw [root_bottomUp v o R i hi]
 rfl

lemma root_event_bounds (v o R start : ℕ) (e : TimedEvent)
 (he : e∈events start (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1) :
 start ≤ e.start ∧ e.stop ≤ start+planDuration (plan v) := by
 have h: e∈treeTimed start (ofPlan (plan v) o):=(root_events v o R start).mem_iff.mp he
 simpa only [ofPlan_duration] using timed_bounds (ofPlan (plan v) o) start e h

end ExactFourierCircuits.UniformCacheTimingEvents

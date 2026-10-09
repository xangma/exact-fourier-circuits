import UniformCacheTimingReverseData
import UniformCacheTimingBounds
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheTimingMetadata
open UniformLocalCacheTreeMachine UniformLocalCacheTreeExecution UniformLocalCacheTreeCoverage
open UniformCacheTimingReverseData UniformCacheTimingBounds UniformCacheTimingMetadata
open UniformLocalRectangleDescriptors UniformLocalCacheTiming UniformBalancedToeplitz

/-- The actual173 traversal, including its physical request addresses. -/
def rootVisits (v o R:ℕ):List Visit:=(walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1
def nodeCount (v o R:ℕ):ℕ:=(rootVisits v o R).length
def requestCount (v o R:ℕ):ℕ:=visitSum (rootVisits v o R)

lemma walk_widths (fuel k c v o:ℕ)(tasks:List Task)(good:Good v o tasks):
 ∀q∈(walk fuel k c tasks).1,q.task.width≤v:=by
 induction fuel generalizing k c tasks with
 | zero=>simp [walk]
 | succ fuel ih=>
  cases tasks with
  | nil=>simp [walk]
  | cons t ts=>
   intro q hq
   simp only [walk,List.mem_cons] at hq
   rcases hq with rfl|hq
   · exact (good t (by simp)).1
   · exact ih (k+1) (c+7*emittedCount t.width) (children t k++ts) (good.children k) q hq
lemma root_width (v o R:ℕ)(q:Visit)(hq:q∈rootVisits v o R):q.task.width≤v:=
 walk_widths (2*v+1) 0 R v o [⟨v,o,0,0⟩]
  (by intro t ht;simp only [List.mem_singleton] at ht;subst t;simp) q hq

/-- Ragged dimensions are bounded by their own original subtree width. -/
lemma current_row_dimensions (t:Task)(a:Row)(ha:a∈currentRows t):a.a+a.e≤t.width:=by
 unfold currentRows at ha
 split_ifs at ha with stop
 · simp at ha
 · unfold rows at ha
   obtain ⟨i,_,hi⟩:=List.mem_flatMap.mp ha
   obtain ⟨j,_,rfl⟩:=List.mem_map.mp hi
   change min _ _+min _ _≤t.width
   have left: min (UniformWorkspacePlanner.selected t.width) (t.width-t.width/2-i*UniformWorkspacePlanner.selected t.width)≤t.width-t.width/2:=
    (min_le_right _ _).trans (Nat.sub_le _ _)
   have right:min (UniformWorkspacePlanner.selected t.width) (t.width/2-j*UniformWorkspacePlanner.selected t.width)≤t.width/2:=
    (min_le_right _ _).trans (Nat.sub_le _ _)
   omega
lemma root_row_budget (v o R B:ℕ)(word:20000*(v+1)≤B)
 (q:Visit)(hq:q∈rootVisits v o R)(a:Row)(ha:a∈currentRows q.task):
 UniformCacheRowDurationMachine.budget a.a a.e≤B:=by
 have dim: a.a+a.e≤v:=(current_row_dimensions q.task a ha).trans (root_width v o R q hq)
 unfold UniformCacheRowDurationMachine.budget
 exact (Nat.mul_le_mul_left 20000 (by omega:a.a+a.e+1≤v+1)).trans word

lemma root_ordinal (v o R i:ℕ)(hi:i<nodeCount v o R):
 ordinal R (rootVisits v o R)[i]=visitSum ((rootVisits v o R).take i):=
 UniformCacheTimingMetadata.root_request_ordinal v o R i hi
lemma root_source (v o R U:ℕ)(extent:R+7*requestCount v o R+4≤U)
 (q:Visit)(hq:q∈rootVisits v o R):q.rectangleBase+7*emittedCount q.task.width+4≤U:=by
 obtain ⟨i,hi,eq⟩:=List.mem_iff_getElem.mp hq
 subst q
 have physBase:=UniformCacheTimingMetadata.walk_rectangle_prefix (2*v+1) 0 R [⟨v,o,0,0⟩] i hi
 have ending:=visitSum_request_end (rootVisits v o R) i hi
 change (rootVisits v o R)[i].rectangleBase=R+7*visitSum ((rootVisits v o R).take i) at physBase
 rw [physBase]
 unfold requestCount at extent
 omega

/-- Every reverse-machine shape and word condition follows from the actual
canonical DFS and ordinary capacities; no duration or start bank is supplied. -/
theorem canonical_metadata (v o R U B:ℕ)
 (source:R+7*requestCount v o R+4≤U)
 (duration:planDuration (plan v)≤B)(rowWord:20000*(v+1)≤B):
 Metadata R U (requestCount v o R) B (rootVisits v o R):=by
 constructor
 · exact root_parentsLE v o R
 · exact root_parentBefore v o R
 · exact root_source v o R U source
 · intro q hq
   obtain ⟨i,hi,eq⟩:=List.mem_iff_getElem.mp hq
   subst q
   rw [root_ordinal v o R i hi,currentRows_length]
   exact visitSum_request_end (rootVisits v o R) i hi
 · intro i j hi hj less
   rw [root_ordinal v o R i hi,root_ordinal v o R j hj,currentRows_length]
   exact visitSum_request_before (rootVisits v o R) i j hi less
 · intro i hi j _
   exact (root_processedSuffix_bound v o R i hi j).trans duration
 · intro q hq
   obtain ⟨i,hi,eq⟩:=List.mem_iff_getElem.mp hq
   subst q
   exact (correction_le _).trans ((root_duration_le v o R i hi).trans duration)
 · exact root_row_budget v o R B rowWord
end ExactFourierCircuits.UniformLocalCacheTimingMetadata

import UniformAxisCacheRequestSource
import UniformAxisCachePreparationRetention
import UniformCacheTimingBounds
import UniformLocalRequestGeometry
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheRequestBounds
open UniformMachine UniformLocalCacheTreeMachine UniformLocalCacheTreeExecution
open UniformLocalCacheTreeCoverage UniformLocalRectangleDescriptors UniformWorkspacePlanner
open UniformLocalRequestPlan UniformAxisCacheRequestSource UniformCacheTimingReference
open UniformAllAxisSeedPreparation UniformJointAllocation UniformAxisCacheSelectedPreparation

lemma walk_good (v o fuel k R:ℕ)(tasks:List Task)(good:Good v o tasks):
 ∀q∈(walk fuel k R tasks).1,q.task.width≤v∧q.task.offset+q.task.width≤o+v:=by
 induction fuel generalizing k R tasks with
 | zero=>simp [walk]
 | succ fuel ih=>
   cases tasks with
   | nil=>simp [walk]
   | cons t ts=>
     intro q hq
     simp only [walk,List.mem_cons] at hq
     rcases hq with rfl|hq
     · exact good t (by simp)
     · exact ih _ _ _ (good.children k) q hq

lemma origin (r R:ℕ)(req:Request)(member:req∈requests (UniformLocalCacheTimingMetadata.rootVisits r 0 R)):
 ∃v o,2≤v∧0<selected v∧o+v≤r∧req.row∈rows v o (selected v):=by
 obtain ⟨q,hq,hreq⟩:=List.mem_flatMap.mp member
 obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hreq
 have fit:=walk_good r 0 (2*r+1) 0 R [⟨r,0,0,0⟩]
  (by intro t ht;simp only [List.mem_singleton] at ht;subst t;exact ⟨le_rfl,le_rfl⟩) q hq
 have active:¬(q.task.width<2∨selected q.task.width=0):=by
  intro bad
  have empty:currentRows q.task=[]:=by rw [currentRows,ite_eq_left bad]
  have length:(currentRows q.task).length=0:=by rw [empty];rfl
  have bound:=j.isLt
  omega
 refine ⟨q.task.width,q.task.offset,by omega,by omega,by omega,?_⟩
 have mem:(currentRows q.task)[j.val]'j.isLt∈currentRows q.task:=List.getElem_mem j.isLt
 simpa only [currentRows,ite_eq_right active] using mem

lemma slotCount_eq (n:ℕ)(q:Row):UniformLocalRequestPlan.slotCount n q=
 UniformJointCacheExtent.slotCount (exponent q.a q.e):=by
 change 352*exponent q.a q.e+330=UniformJointCacheExtent.slotCount (exponent q.a q.e)
 exact (UniformJointCacheExtent.slotCount_formula _).symm
lemma prefix_total (n:ℕ)(qs:List Request):slotPrefix n qs qs.length=
 (qs.map (fun q=>UniformLocalRequestPlan.slotCount n q.row)).sum:=by
 induction qs with
 | nil=>rfl
 | cons q qs ih=>simpa only [List.length_cons,slotPrefix,List.map_cons,List.sum_cons] using congrArg (UniformLocalRequestPlan.slotCount n q.row+·) ih

/-- The real request list leaves the allocator's two-r-squared reserve for
both leaf orientations; the rectangle count is not supplied as a premise. -/
lemma capacity (n r R:ℕ):
 slotPrefix n (requests (UniformLocalCacheTimingMetadata.rootVisits r 0 R))
  (requests (UniformLocalCacheTimingMetadata.rootVisits r 0 R)).length+2*r^2≤
 UniformJointCacheExtent.capacity r:=by
 have eq:=congrArg (fun rs:List Row=>(rs.map (fun q=>UniformJointCacheExtent.slotCount (exponent q.a q.e))).sum)
  (requests_rows (UniformLocalCacheTimingMetadata.rootVisits r 0 R))
 simp only [List.map_map,Function.comp_def] at eq
 rw [prefix_total]
 simp_rw [slotCount_eq]
 rw [eq]
 exact UniformJointCacheExtent.actual_walk_slots r 0 R

lemma rectangle_duration (n:ℕ)(q:Row):UniformLocalCacheTiming.rectangleDuration q=
 28*UniformLocalRequestPlan.slotCount n q:=by
 change 28*(4*(8*exponent q.a q.e+7)+2)*11=28*(352*exponent q.a q.e+330)
 ring
lemma node_event (q:Visit)(req:Request)(member:req∈nodeRequests q):
 (⟨req.time,.rectangle req.row⟩:UniformLocalCacheTiming.TimedEvent)∈UniformCacheTimingEvents.nodeEvents 0 q.task:=by
 obtain ⟨j,rfl⟩:=List.mem_ofFn.mp member
 have active:¬(q.task.width<2∨selected q.task.width=0):=by
  intro bad
  have empty:currentRows q.task=[]:=by rw [currentRows,ite_eq_left bad]
  have length:(currentRows q.task).length=0:=by rw [empty];rfl
  have bound:=j.isLt
  omega
 have entry:=UniformCacheTimingEvents.requestStart_index q j.val j.isLt
 have mem:=List.getElem_mem (l:=UniformLocalCacheTiming.sequenceRows
   (taskDuration q.task-correction q) (currentRows q.task))
   (by rw [UniformLocalCacheTiming.sequenceRows_length];exact j.isLt)
 rw [entry] at mem
 simpa only [UniformCacheTimingEvents.nodeEvents,ite_eq_right active,Nat.zero_add,correction] using mem
lemma time_bound (n r R:ℕ)(req:Request)
 (member:req∈requests (UniformLocalCacheTimingMetadata.rootVisits r 0 R)):
 req.time+28*UniformLocalRequestPlan.slotCount n req.row≤
 UniformLocalCacheTiming.planDuration (UniformBalancedToeplitz.plan r):=by
 obtain ⟨q,hq,hreq⟩:=List.mem_flatMap.mp member
 have event: (⟨req.time,.rectangle req.row⟩:UniformLocalCacheTiming.TimedEvent)∈
  UniformCacheTimingEvents.events 0 (UniformLocalCacheTimingMetadata.rootVisits r 0 R):=
  List.mem_flatMap.mpr ⟨q,hq,node_event q req hreq⟩
 have bound:=(UniformCacheTimingEvents.root_event_bounds r 0 R 0 _ event).2
 simpa only [UniformLocalCacheTiming.TimedEvent.stop,UniformLocalCacheTiming.Event.duration,
  rectangle_duration n,Nat.zero_add] using bound

end ExactFourierCircuits.UniformAxisCacheRequestBounds

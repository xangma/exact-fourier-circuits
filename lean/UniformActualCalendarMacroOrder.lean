import UniformAxisCacheRequestSource
import UniformCalendarPermutationActive

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarMacroOrder
noncomputable section
open UniformLocalCacheTreeMachine UniformLocalRequestPlan UniformAxisCacheRequestSource
open UniformLocalCacheTiming UniformCacheTimingEvents UniformWorkspacePlanner
open UniformLocalCacheTreeExecution UniformLocalCacheTreeCoverage UniformCacheTimingReference

abbrev rectangleEvent (q:Request):TimedEvent:=⟨q.time,.rectangle q.row⟩
def directEvents (q:Visit):List TimedEvent:=
 if q.task.width<2 ∨selected q.task.width=0 then [⟨0,.direct q.task.width q.task.offset⟩] else []
def preparationEvents (visits:List Visit):List TimedEvent:=
 (requests visits).map rectangleEvent++visits.flatMap directEvents

lemma node_requests_events (q:Visit):
 (nodeRequests q).map rectangleEvent++directEvents q=nodeEvents 0 q.task:=by
 by_cases bad:q.task.width<2 ∨selected q.task.width=0
 · have empty:currentRows q.task=[]:=by rw[currentRows,ite_eq_left bad]
   simp only[nodeRequests,empty,List.length_nil,List.ofFn_zero,List.map_nil,
    directEvents,bad,ite_true,List.nil_append,nodeEvents]
 · have none:directEvents q=[]:=by rw[directEvents,ite_eq_right bad]
   rw[none,List.append_nil,nodeEvents,ite_eq_right bad,Nat.zero_add]
   apply List.ext_getElem
   · simp only[List.length_map,nodeRequests,List.length_ofFn,sequenceRows_length]
   · intro i hi hj
     have bound:i<(currentRows q.task).length:=by simpa only[sequenceRows_length] using hj
     have actual:=requestStart_index q i bound
     simpa only[List.getElem_map,nodeRequests,List.getElem_ofFn,rectangleEvent,correction] using actual.symm

lemma flatMap_partition {α β:Type}(xs:List α)(f g:α→List β):
 (xs.flatMap f++xs.flatMap g).Perm (xs.flatMap (fun a=>f a++g a)):=by
 induction xs with
 | nil=>exact List.Perm.refl _
 | cons a xs ih=>
  simp only[List.flatMap_cons]
  have swap:((f a++xs.flatMap f)++(g a++xs.flatMap g)).Perm
   ((f a++g a)++(xs.flatMap f++xs.flatMap g)):=by
   simpa only[List.append_assoc] using
    (List.Perm.refl (f a)).append ((List.perm_append_comm (l₁:=xs.flatMap f) (l₂:=g a)).append_right (xs.flatMap g))
  exact swap.trans ((List.Perm.refl _).append ih)

/-- The physical cache's rectangle-first/node-second order is a permutation
of the genuine preparation walk's macro events. -/
theorem preparation_perm (visits:List Visit):
 (preparationEvents visits).Perm (UniformCacheTimingEvents.events 0 visits):=by
 have perm:=flatMap_partition visits (fun q=>(nodeRequests q).map rectangleEvent) directEvents
 simpa only[preparationEvents,requests,List.map_flatMap,Function.comp_def,
  node_requests_events,UniformCacheTimingEvents.events] using perm

/-- Canonical actual stored requests plus corrected time-zero direct ranges
recover the original parallel tree calendar without an alignment assumption. -/
theorem root_preparation_perm (v o R:ℕ):
 (preparationEvents (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1).Perm
 (treeTimed 0 (ofPlan (UniformBalancedToeplitz.plan v) o)):=
 (preparation_perm _).trans (root_events v o R 0)

end
end ExactFourierCircuits.UniformActualCalendarMacroOrder

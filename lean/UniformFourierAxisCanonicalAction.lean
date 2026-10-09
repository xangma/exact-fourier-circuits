import UniformFourierAxisCommonBounds
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisCanonicalAction
open UniformMachine UniformJointAllocation UniformJointCacheAllocation UniformAllAxisSeedPreparation
open UniformFourierAxisCommonResult UniformFourierAxisCanonicalEvents UniformCalendarAxisAction
noncomputable section

lemma boundary_family{d g:ℕ}(boundary:UniformFourierAxisPrepareBoundary.BoundaryAt d g):
 UniformFourierAxisPrepareBoundary.FamilyAt d g (boundaryLane d g):=by
 classical
 by_cases h:g=0∨g=2*d+4
 · exact Or.inl ⟨h,by simp only[boundaryLane,ite_eq_left h,Fin.val_zero]⟩
 · by_cases middle:g=d+1∨g=d+3
   · exact Or.inr (Or.inl ⟨middle,by simp only[boundaryLane,ite_eq_right h,ite_eq_left middle,Fin.val_one]⟩)
   · refine Or.inr (Or.inr ⟨?_,?_⟩)
     · unfold UniformFourierAxisPrepareBoundary.BoundaryAt at boundary
       omega
     · simp only[boundaryLane,ite_eq_right h,ite_eq_right middle]
       rfl

/-- The clock alone determines the true retained boundary diagonal. This pure
Action needs no execution result, selected-bank certificate or action premise. -/
def boundary{c:Constants}{n g:ℕ}(hn:0<n)(j:Fin (ell n))(treeEvents:ℕ→List UniformGlobalCalendarDispatch.Event)
 (atBoundary:UniformFourierAxisPrepareBoundary.BoundaryAt (depth n j) g):
 Action (radix n j) (events c n g j treeEvents) (UniformReflectedFourierCalendar.specified (radix n j) g).matrix:=by
 unfold events
 rw[eventsAt_boundary treeEvents atBoundary]
 have positive:0<radix n j:=lt_of_lt_of_le (by decide:0<2)
  (UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn j)
 exact UniformCalendarAxisAction.congr (UniformAxisBoundaryEvents.action (radix n j) (slab c n)
  (UniformFourierAxisWorkspace.axis c n j).boundary (OAI.ExactFourier.zeta (radix n j)) (boundaryLane (depth n j) g))
   (UniformAxisBoundarySelectedClock.specified_boundary positive g (boundaryLane (depth n j) g)
    (boundary_family atBoundary)).symm

/-- Once the actual axis calendar has ended, its canonical list is empty and
its matrix is the identity, independently of all mutable machine state. -/
def inactive{c:Constants}{n g:ℕ}(hn:0<n)(j:Fin (ell n))(treeEvents:ℕ→List UniformGlobalCalendarDispatch.Event)
 (finished:2*depth n j+5≤g):
 Action (radix n j) (events c n g j treeEvents) (UniformReflectedFourierCalendar.specified (radix n j) g).matrix:=by
 unfold events
 rw[eventsAt_inactive treeEvents finished]
 have positive:0<radix n j:=lt_of_lt_of_le (by decide:0<2)
  (UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn j)
 exact UniformCalendarAxisAction.congr (UniformAxisBoundarySemantics.empty_action (radix n j))
  (UniformAxisBoundarySelectedClock.specified_inactive positive g finished).symm

lemma boundary_nonempty{c:Constants}{n g:ℕ}(hn:0<n)(j:Fin (ell n))(treeEvents:ℕ→List UniformGlobalCalendarDispatch.Event)
 (atBoundary:UniformFourierAxisPrepareBoundary.BoundaryAt (depth n j) g):
 Nonempty (Action (radix n j) (events c n g j treeEvents) (UniformReflectedFourierCalendar.specified (radix n j) g).matrix):=
 ⟨boundary hn j treeEvents atBoundary⟩
lemma inactive_nonempty{c:Constants}{n g:ℕ}(hn:0<n)(j:Fin (ell n))(treeEvents:ℕ→List UniformGlobalCalendarDispatch.Event)
 (finished:2*depth n j+5≤g):
 Nonempty (Action (radix n j) (events c n g j treeEvents) (UniformReflectedFourierCalendar.specified (radix n j) g).matrix):=
 ⟨inactive hn j treeEvents finished⟩
end
end ExactFourierCircuits.UniformFourierAxisCanonicalAction

import UniformFourierAxisOperationalOutside
import UniformAxisBoundarySemantics

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisCanonicalEvents
open UniformMachine UniformJointAllocation UniformJointCacheAllocation UniformGlobalCalendarDispatch
open UniformFourierAxisOperationalCases
noncomputable section
local instance (d g:ℕ):Decidable (TreeAt d g):=by unfold TreeAt;infer_instance
local instance (d g:ℕ):Decidable (UniformFourierAxisPrepareBoundary.BoundaryAt d g):=by
 unfold UniformFourierAxisPrepareBoundary.BoundaryAt;infer_instance

/-- The actual three boundary lanes, determined solely by the original clock. -/
def boundaryLane(d g:ℕ):Fin 3:=
 if g=0∨g=2*d+4 then 0 else if g=d+1∨g=d+3 then 1 else 2

lemma family_lane {d g:ℕ}{q:Fin 3}
 (family:UniformFourierAxisPrepareBoundary.FamilyAt d g q):q=boundaryLane d g:=by
 apply Fin.ext
 rcases family with zero|one|two
 · simp only[boundaryLane,ite_eq_left zero.1,Fin.val_zero]
   exact zero.2
 · have other:¬(g=0∨g=2*d+4):=by omega
   simp only[boundaryLane,ite_eq_right other,ite_eq_left one.1]
   exact one.2
 · have other:¬(g=0∨g=2*d+4):=by omega
   have middle:¬(g=d+1∨g=d+3):=by omega
   simp only[boundaryLane,ite_eq_right other,ite_eq_right middle]
   exact two.2

lemma family_boundary {d g:ℕ}{q:Fin 3}
 (family:UniformFourierAxisPrepareBoundary.FamilyAt d g q):UniformFourierAxisPrepareBoundary.BoundaryAt d g:=by
 unfold UniformFourierAxisPrepareBoundary.FamilyAt at family
 unfold UniformFourierAxisPrepareBoundary.BoundaryAt
 omega

lemma boundary_not_tree{d g:ℕ}(boundary:UniformFourierAxisPrepareBoundary.BoundaryAt d g):¬TreeAt d g:=by
 unfold UniformFourierAxisPrepareBoundary.BoundaryAt at boundary
 unfold TreeAt
 omega

/-- Canonical per-axis events at every global clock. The TREE function is the
unchanged retained cache Bundle.events; the other branches use literal lanes. -/
def eventsAt(c:Constants)(n:ℕ)(j:Fin (ell n))(d g:ℕ)(treeEvents:ℕ→List Event):List Event:=
 if TreeAt d g then treeEvents (UniformFourierAxisPrepareTree.localTick d g)
 else if UniformFourierAxisPrepareBoundary.BoundaryAt d g then
  UniformAxisBoundaryBindings.events c n j (boundaryLane d g) else []

lemma eventsAt_tree{c:Constants}{n d g:ℕ}{j:Fin (ell n)}(treeEvents:ℕ→List Event)(tree:TreeAt d g):
 eventsAt c n j d g treeEvents=treeEvents (UniformFourierAxisPrepareTree.localTick d g):=by simp only[eventsAt,ite_eq_left tree]

lemma eventsAt_boundary{c:Constants}{n d g:ℕ}{j:Fin (ell n)}(treeEvents:ℕ→List Event)
 (boundary:UniformFourierAxisPrepareBoundary.BoundaryAt d g):
 eventsAt c n j d g treeEvents=UniformAxisBoundaryBindings.events c n j (boundaryLane d g):=by
 simp only[eventsAt,ite_eq_right (boundary_not_tree boundary),ite_eq_left boundary]

lemma eventsAt_inactive{c:Constants}{n d g:ℕ}{j:Fin (ell n)}(treeEvents:ℕ→List Event)(inactive:2*d+5≤g):
 eventsAt c n j d g treeEvents=[]:=by
 have tree:¬TreeAt d g:=by unfold TreeAt;omega
 have boundary:¬UniformFourierAxisPrepareBoundary.BoundaryAt d g:=by
  unfold UniformFourierAxisPrepareBoundary.BoundaryAt;omega
 simp only[eventsAt,ite_eq_right tree,ite_eq_right boundary]

/-- Actual389 boundary execution facts, with the exact clock-canonical list. -/
theorem boundary {c:Constants}{n g:ℕ}{hn:0<n}{j:Fin (ell n)}{q:Fin 3}
 {x:Fin n→ℂ}{s u:State}(treeEvents:ℕ→List Event)
 (actual:UniformFourierAxisPrepareBoundary.Result c n
  (UniformAxisBoundarySelectedClock.depth (UniformAllAxisSeedPreparation.radix n j)) g hn j q x s u):
 let es:=eventsAt c n j (UniformAxisBoundarySelectedClock.depth (UniformAllAxisSeedPreparation.radix n j)) g treeEvents
 Selections (UniformFourierAxisWorkspace.axis c n j).selected 0 es u∧
 (∀e∈es,CachedEvent (UniformAllAxisSeedPreparation.radix n j) (UniformFourierAxisWorkspace.axis c n j).pool
  (UniformFourierAxisWorkspace.axis c n j).rawRows (envelope c n) e u)∧
 Nonempty (UniformCalendarAxisAction.Action (UniformAllAxisSeedPreparation.radix n j) es
  (UniformReflectedFourierCalendar.specified (UniformAllAxisSeedPreparation.radix n j) g).matrix):=by
 dsimp only
 rw[eventsAt_boundary treeEvents (family_boundary actual.family),←family_lane actual.family]
 exact UniformAxisBoundarySemantics.boundary actual

/-- Actual389 inactive execution facts use the same canonical event function. -/
theorem inactive {c:Constants}{n g:ℕ}(hn:0<n){j:Fin (ell n)}
 {x:Fin n→ℂ}{s u:State}(treeEvents:ℕ→List Event)
 (actual:UniformFourierAxisPrepareInactive.Result c n
  (UniformAxisBoundarySelectedClock.depth (UniformAllAxisSeedPreparation.radix n j)) g j x s u):
 let es:=eventsAt c n j (UniformAxisBoundarySelectedClock.depth (UniformAllAxisSeedPreparation.radix n j)) g treeEvents
 Selections (UniformFourierAxisWorkspace.axis c n j).selected 0 es u∧
 (∀e∈es,CachedEvent (UniformAllAxisSeedPreparation.radix n j) (UniformFourierAxisWorkspace.axis c n j).pool
  (UniformFourierAxisWorkspace.axis c n j).rawRows (envelope c n) e u)∧
 Nonempty (UniformCalendarAxisAction.Action (UniformAllAxisSeedPreparation.radix n j) es
  (UniformReflectedFourierCalendar.specified (UniformAllAxisSeedPreparation.radix n j) g).matrix):=by
 dsimp only
 rw[eventsAt_inactive treeEvents (UniformAxisBoundarySemantics.inactive_clock actual.selected actual.mode)]
 exact UniformAxisBoundarySemantics.inactive hn actual

end
end ExactFourierCircuits.UniformFourierAxisCanonicalEvents

import UniformFourierAxisCanonicalEvents
import UniformFourierAxisTreeRegistryFacts

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisPhaseReadBounds
open UniformMachine UniformJointAllocation UniformJointCacheAllocation UniformGlobalCalendarDispatch
open UniformFourierAxisCanonicalEvents
noncomputable section

/-- The boundary descriptor ends exactly at phase; no source read reaches the
fresh raw-row output bank used by the following dispatcher. -/
lemma boundary_payload{c:Constants}{n g:ℕ}{hn:0<n}{j:Fin (ell n)}{q:Fin 3}{s:State}
 (actual:UniformFourierAxisPrepareBoundary.Payload c n g hn j q s):
 CachedEvent (UniformAllAxisSeedPreparation.radix n j) (UniformFourierAxisWorkspace.axis c n j).pool
  (UniformFourierAxisWorkspace.axis c n j).phase (envelope c n)
  (UniformAxisBoundaryEvents.event (UniformAllAxisSeedPreparation.radix n j) (slab c n)
   (UniformFourierAxisWorkspace.axis c n j).boundary (OAI.ExactFourier.zeta (UniformAllAxisSeedPreparation.radix n j)) q) s:=by
 have geo:=UniformFourierAxisGeometry.geometry c hn j
 have layout:=UniformFourierAxisWorkspace.axis_geometry c n j
 exact UniformAxisBoundaryEvents.event_cached geo.radix actual.stored actual.pools layout.2.1.le geo.boundaryMerged

lemma boundary {c:Constants}{n g:ℕ}{hn:0<n}{j:Fin (ell n)}{q:Fin 3}
 {x:Fin n→ℂ}{s u:State}(treeEvents:ℕ→List Event)
 (actual:UniformFourierAxisPrepareBoundary.Result c n
  (UniformAxisBoundarySelectedClock.depth (UniformAllAxisSeedPreparation.radix n j)) g hn j q x s u):
 ∀e∈eventsAt c n j (UniformAxisBoundarySelectedClock.depth (UniformAllAxisSeedPreparation.radix n j)) g treeEvents,
 CachedEvent (UniformAllAxisSeedPreparation.radix n j) (UniformFourierAxisWorkspace.axis c n j).pool
  (UniformFourierAxisWorkspace.axis c n j).phase (envelope c n) e u:=by
 rw[eventsAt_boundary treeEvents (family_boundary actual.family),←family_lane actual.family]
 intro e he
 have same:e=UniformAxisBoundaryEvents.event (UniformAllAxisSeedPreparation.radix n j) (slab c n)
  (UniformFourierAxisWorkspace.axis c n j).boundary (OAI.ExactFourier.zeta (UniformAllAxisSeedPreparation.radix n j)) q:=by
  simpa only[UniformAxisBoundaryBindings.events,List.mem_singleton] using he
 subst e
 exact boundary_payload actual.payload

lemma tree {c:Constants}{n d g O T:ℕ}{j:Fin (ell n)}
 {L:List (ℕ×ℕ)}{nodes:List UniformCacheRangeSelector.Range}{x:Fin n→ℂ}{s u:State}
 (bundle:UniformActualCalendarRegistry.Bundle (UniformAllAxisSeedPreparation.radix n j) O T
  (envelope c n) ((UniformJointCacheAllocation.axis c n j).control+3*UniformAllAxisSeedPreparation.radix n j+4) L nodes s)
 (actual:UniformFourierAxisPrepareTree.Result c n d g L.length j
  (fun i=>L[i]?.getD (0,0)) nodes x s u)
 (readNat:T≤(UniformFourierAxisWorkspace.axis c n j).selected)
 (scalar:O≤(UniformFourierAxisWorkspace.axis c n j).pool):
 ∀e∈bundle.events (UniformFourierAxisPrepareTree.localTick d g),
 CachedEvent (UniformAllAxisSeedPreparation.radix n j) (UniformFourierAxisWorkspace.axis c n j).pool
  (UniformFourierAxisWorkspace.axis c n j).phase (envelope c n) e u:=by
 have geometry:=UniformFourierAxisWorkspace.axis_geometry c n j
 have nat:T≤(UniformFourierAxisWorkspace.axis c n j).phase:=by omega
 have keep:∀z,z<T→u.natHeap z=s.natHeap z:=by
  intro z hz
  rw[actual.bank]
  exact UniformCacheRangeSelector.writeSelections_low _ _ _ _ _ (hz.trans_le readNat)
 intro e he
 exact UniformFourierAxisTreeRegistryFacts.cached_mono
  ((bundle.cached _ e he).transfer keep (fun z _=>congrFun actual.scalarHeap z)) scalar nat

end
end ExactFourierCircuits.UniformFourierAxisPhaseReadBounds

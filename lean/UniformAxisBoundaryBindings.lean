import UniformAxisBoundaryEvents

set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisBoundaryBindings
noncomputable section
open UniformMachine UniformGlobalCalendarDispatch UniformAxisBoundaryEvents
open UniformJointAllocation UniformJointCacheAllocation UniformAllAxisSeedPreparation
open UniformFourierAxisPrepareBoundary

lemma payload_cached {c:Constants}{n g:ℕ}{hn:0<n}{j:Fin (ell n)}{q:Fin 3}{s:State}
 (h:Payload c n g hn j q s):
 CachedEvent (radix n j) (W.axis c n j).pool (W.axis c n j).rawRows (envelope c n)
  (event (radix n j) (slab c n) (W.axis c n j).boundary (OAI.ExactFourier.zeta (radix n j)) q) s:=by
 have geo:=UniformFourierAxisGeometry.geometry c hn j
 have layout:=UniformFourierAxisWorkspace.axis_geometry c n j
 have fit:(W.axis c n j).boundary+3*radix n j+11≤(W.axis c n j).rawRows:=by
  omega
 exact event_cached geo.radix h.stored h.pools fit geo.boundaryMerged

def events (c:Constants)(n:ℕ)(j:Fin (ell n))(q:Fin 3):List Event:=
 [event (radix n j) (slab c n) (W.axis c n j).boundary (OAI.ExactFourier.zeta (radix n j)) q]

lemma factual {c:Constants}{n d g:ℕ}{hn:0<n}{j:Fin (ell n)}{q:Fin 3}
 {x:Fin n→ℂ}{s u:State}(actual:Result c n d g hn j q x s u):
 Selections (W.axis c n j).selected 0 (events c n j q) u ∧
 ∀e∈events c n j q,CachedEvent (radix n j) (W.axis c n j).pool (W.axis c n j).rawRows
  (envelope c n) e u:=by
 refine ⟨selections actual.payload.selected,?_⟩
 intro e he
 have eq:e=event (radix n j) (slab c n) (W.axis c n j).boundary (OAI.ExactFourier.zeta (radix n j)) q:=by
  simpa only[events,List.mem_singleton] using he
 subst e
 exact payload_cached actual.payload

end
end ExactFourierCircuits.UniformAxisBoundaryBindings

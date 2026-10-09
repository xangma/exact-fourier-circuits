import UniformActualCalendarRootAtoms
import UniformCalendarAtomSourceTransport

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarNativeRootAction
noncomputable section
open OAI.ExactFourier UniformActualCalendarRegistry UniformLocalCacheTreeMachine
open UniformCalendarActualAtoms UniformCalendarAtomCollapse UniformCalendarRefinementActive
open UniformActualCalendarMacroOrder UniformCalendarIntervalPartition UniformLocalFourierLayers
open UniformLocalCacheTiming UniformGlobalCalendarUnion UniformGlobalCalendarGeometry
open UniformCalendarNativePieces UniformActualCalendarRectanglePhaseResult UniformCalendarAtomSourceTransport
open UniformCalendarRenderSnapshot UniformCalendarNativeRenderFamily

abbrev visits (v o R:ℕ):List Visit:=(walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1
abbrev macros (v o R:ℕ):List TimedEvent:=preparationEvents (visits v o R)
abbrev Atoms (n v o R t:ℕ):Type:=ActiveAtom (macros v o R) (pieces n (macros v o R)) t

def atomEvent (n v o R t:ℕ)(make:ℕ→ℕ→UniformGlobalCalendarDispatch.Event)(a:Atoms n v o R t):
 UniformGlobalCalendarDispatch.Event:=
 make (UniformCalendarRefinementActive.order n (macros v o R) a.val).val
  (t-((macros v o R).get a.val.1).start-
   prefixDuration (pieces n (macros v o R) a.val.1) a.val.2.val)

variable (n v o R:ℕ)(p:UniformDirectLeafForestData.Parameters)(A t r:ℕ)
 {cacheRadix O T B D:ℕ}{s:UniformMachine.State}
 (b:Bundle cacheRadix O T B D
  (UniformActualCacheRectangleSource.entries n (UniformAxisCacheRequestSource.requests (visits v o R)))
  (UniformDirectLeafForestRangeSource.nodeRanges p (visits v o R) A) s)
 (extent:o+v≤r)(f:PowerSeries ℂ)(hf:PowerSeries.constantCoeff f≠0)

-- Internal assembly interface: the concrete rectangle/direct constructor
-- discharges produce from actual factories, rather than taking it as final evidence.
def sourceMatch
 (produce:∀(a:Atoms n v o R t)
  (fit:Event.low ((macros v o R).get a.val.1).event+Event.width ((macros v o R).get a.val.1).event≤r)
  (L:List (Layer (Event.width ((macros v o R).get a.val.1).event))),
  Core f hf ((macros v o R).get a.val.1).event L→
  Result (atomEvent n v o R t b.scan.make a)
   (UniformChunkPortMachine.intervalEmbedding r (Event.low ((macros v o R).get a.val.1).event)
    (Event.width ((macros v o R).get a.val.1).event) fit) L (t-((macros v o R).get a.val.1).start))
 (i:Fin (b.events t).length):
 Match ((b.events t).get i)
  ((Embedded.sigmaIn (UniformActualCalendarRootAtoms.enumeration n v o R p A t b i)).trans
   (treeEmbedding (UniformBalancedToeplitz.plan v) o 0 t r extent))
  (renderFamily (UniformBalancedToeplitz.plan v) o 0 t f hf
   (UniformActualCalendarRootAtoms.enumeration n v o R p A t b i)):=by
 let a:=UniformActualCalendarBundleAtoms.enumeration n p (visits v o R) A t b i
 let original:=UniformActualCalendarRootAtoms.enumeration n v o R p A t b i
 have same:=UniformActualCalendarRootAtoms.descriptor n v o R p A t b i
 have fit:Event.low ((macros v o R).get a.val.1).event+Event.width ((macros v o R).get a.val.1).event≤r:=by
  rw[←same,←event_high]
  have bounds:=tree_band (UniformBalancedToeplitz.plan v) o 0 _
   (List.get_mem _ original.val)
  change Event.high ((treeTimed 0 (ofPlan (UniformBalancedToeplitz.plan v) o)).get original.val).event≤r
  exact bounds.2.trans extent
 apply Classical.choice
 obtain ⟨L,native,matrix⟩:=renderFamily_native (UniformBalancedToeplitz.plan v) o 0 t f hf original
 let result:=native_result r t f hf _ _ same fit
  ((Embedded.sigmaIn original).trans (treeEmbedding (UniformBalancedToeplitz.plan v) o 0 t r extent))
  (fun _=>rfl) (atomEvent n v o R t b.scan.make a) (produce a fit) L native
 have eq:(b.events t).get i=atomEvent n v o R t b.scan.make a:=by
  have value:=UniformActualCalendarBundleAtoms.event n p (visits v o R) A t b i
  simpa only[atomEvent,Nat.sub_add_eq] using value
 refine ⟨⟨result.snapshot,?_,result.matrix.trans matrix.symm⟩⟩
 rw[eq]
 exact result.source

def action
 (produce:∀(a:Atoms n v o R t)
  (fit:Event.low ((macros v o R).get a.val.1).event+Event.width ((macros v o R).get a.val.1).event≤r)
  (L:List (Layer (Event.width ((macros v o R).get a.val.1).event))),
  Core f hf ((macros v o R).get a.val.1).event L→
  Result (atomEvent n v o R t b.scan.make a)
   (UniformChunkPortMachine.intervalEmbedding r (Event.low ((macros v o R).get a.val.1).event)
    (Event.width ((macros v o R).get a.val.1).event) fit) L (t-((macros v o R).get a.val.1).start)):
 UniformCalendarAxisAction.Action r (b.events t)
  (treeSnapshot (UniformBalancedToeplitz.plan v) o 0 t r extent
   (renderFamily (UniformBalancedToeplitz.plan v) o 0 t f hf)).matrix:=by
 let m:=sourceMatch n v o R p A t r b extent f hf produce
 exact UniformCalendarPulledSourceAction.action
  (UniformActualCalendarRootAtoms.enumeration n v o R p A t b)
  (treeEmbedding (UniformBalancedToeplitz.plan v) o 0 t r extent)
  (fun i=>(m i).snapshot) (renderFamily (UniformBalancedToeplitz.plan v) o 0 t f hf)
  (fun i=>(m i).source) (fun i=>(m i).matrix)

end
end ExactFourierCircuits.UniformCalendarNativeRootAction

import UniformActualCalendarMatchingSource
import UniformLocalCacheSlotInvariant

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRectangleEvent
open UniformMachine UniformLocalFactorDispatchMachine
open UniformLocalCacheSlotConductorMachine
open UniformActualCalendarMatchingSource
open UniformGlobalCalendarDispatch
open UniformGlobalMatchingScaleMachine (Phase)
noncomputable section

variable {B : ℕ} (c : Header.Parameters) (q : UniformLocalRectangleDescriptors.Row)
 (slot : UniformLocalCacheChronology.Slot)
 (l : UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B)
 (bl : BroadcastLayout c q B)
 (ha : q.a≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (he : q.e≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (bank : Fin (UniformToeplitzCrossDAG.bankSize c.height.K)→ℂ)

def values : Fin 9→Fin c.ambient→ℂ:=
 fun lane i=>(entry c q slot l bl ha he bank).value lane
  (Fin.cast (entry_radix c q slot l bl ha he bank).symm i)
def edges : Fin (printedRows c q slot l bl ha he).length→UniformColoring.Edge:=
 UniformGlobalMatchingScaleBankBridge.rowEdges (printedRows c q slot l bl ha he)
  (dispatched_geometry c q slot l bl ha he).2.1

def actualEvent (elapsed : ℕ) (phase : Phase) : Event:=
 event c.cacheDirectory elapsed c.pool c.cachePermutation c.kind phase
  (values c q slot l bl ha he bank) (edges c q slot l bl ha he)

/-- Real rectangle Cached contents give the physical dispatcher's exact
source factors and ordered endpoints. Capacity follows from its generated
matching; only ordinary address separation remains with the allocator. -/
theorem cached {O T : ℕ} (elapsed : ℕ) (phase : Phase) (s : State)
 (positive : 2≤c.ambient) (contents : Contents c q slot l bl ha he bank positive s)
 (decoded : Decoded (actualEvent c q slot l bl ha he bank elapsed phase).descriptor phase)
 (entryFit : c.cacheDirectory+7≤T) (poolFit : c.pool+9*c.ambient≤O)
 (permutationFit : c.cachePermutation+c.ambient≤T) (radixBound : c.ambient≤B) :
 CachedEvent c.ambient O T B (actualEvent c q slot l bl ha he bank elapsed phase) s:=by
 have geometry:=dispatched_geometry c q slot l bl ha he
 have matching:=UniformGlobalMatchingScaleBankBridge.rowEdges_matching
  (printedRows c q slot l bl ha he) geometry.2.1 geometry.2.2
 have range:=UniformGlobalMatchingScaleBankBridge.rowEdges_range c.ambient
  (printedRows c q slot l bl ha he) geometry.2.1 geometry.1
 have pools:=pool_grid (entry c q slot l bl ha he bank)
  (entry_radix c q slot l bl ha he bank) (entry_pool c q slot l bl ha he bank) s contents.factors
 exact cached_event (edges c q slot l bl ha he) matching range positive phase
  (values c q slot l bl ha he bank) s decoded contents.abi pools contents.permutation
  entryFit poolFit permutationFit radixBound

/-- Real decoder policy for an active ordinary entry at its literal elapsed
phase. Empty generated matchings remain valid events. -/
theorem ordinary_cached {O T : ℕ} (elapsed : ℕ) (bound : elapsed<28) (s : State)
 (positive : 2≤c.ambient) (contents : Contents c q slot l bl ha he bank positive s)
 (kind : c.kind=0) (entryFit : c.cacheDirectory+7≤T) (poolFit : c.pool+9*c.ambient≤O)
 (permutationFit : c.cachePermutation+c.ambient≤T) (radixBound : c.ambient≤B) :
 CachedEvent c.ambient O T B
  (actualEvent c q slot l bl ha he bank elapsed
   (UniformGlobalMatchingScaleMachine.phases.get ⟨elapsed,by rw[UniformGlobalMatchingScaleMachine.phases_length];exact bound⟩)) s:=by
 apply cached c q slot l bl ha he bank elapsed _ s positive contents _ entryFit poolFit permutationFit radixBound
 exact Or.inl ⟨bound,kind,rfl⟩

end
end ExactFourierCircuits.UniformActualCalendarRectangleEvent

import UniformFourierAxisOperationalFrames
import UniformActualCalendarRegistryOutput

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisTreeRegistryFacts
open UniformMachine UniformJointAllocation UniformJointCacheAllocation UniformGlobalCalendarDispatch
noncomputable section

/-- Weakening a read bound does not change any descriptor, source cell, event,
or matrix. This is separate from transporting through an actual heap change. -/
lemma cached_mono{r O T O' T' B:ℕ}{e:Event}{s:State}(actual:CachedEvent r O T B e s)
 (scalar:O≤O')(nat:T≤T'):CachedEvent r O' T' B e s:=
 ⟨actual.decoded,actual.stored,actual.source,actual.entryFit.trans nat,
  actual.sourcePool.trans scalar,actual.sourceRows.trans nat,actual.matching,actual.values⟩

/-- The real TREE selector stores precisely the retained Bundle's events.
Its writes are above every source cache cell, so source facts survive and are
then weakened to the actual merged output bounds. -/
theorem factual{c:Constants}{n d g O T:ℕ}{j:Fin (ell n)}
 {L:List (ℕ×ℕ)}{nodes:List UniformCacheRangeSelector.Range}{x:Fin n→ℂ}{s u:State}
 (bundle:UniformActualCalendarRegistry.Bundle (UniformAllAxisSeedPreparation.radix n j) O T
  (envelope c n) ((UniformJointCacheAllocation.axis c n j).control+3*UniformAllAxisSeedPreparation.radix n j+4) L nodes s)
 (actual:UniformFourierAxisPrepareTree.Result c n d g L.length j
  (fun i=>L[i]?.getD (0,0)) nodes x s u)
 (readNat:T≤(UniformFourierAxisWorkspace.axis c n j).selected)
 (scalar:O≤(UniformFourierAxisWorkspace.axis c n j).pool):
 let es:=bundle.events (UniformFourierAxisPrepareTree.localTick d g)
 Selections (UniformFourierAxisWorkspace.axis c n j).selected 0 es u∧
 (∀e∈es,CachedEvent (UniformAllAxisSeedPreparation.radix n j)
  (UniformFourierAxisWorkspace.axis c n j).pool (UniformFourierAxisWorkspace.axis c n j).rawRows
  (envelope c n) e u)∧
 es.length=UniformFourierAxisPrepareTree.count c n d g L.length j (fun i=>L[i]?.getD (0,0)) nodes:=by
 dsimp only
 have pair:=bundle.pairs (UniformFourierAxisPrepareTree.localTick d g)
 have eq:UniformActualCalendarSelectionBank.pairs (bundle.events (UniformFourierAxisPrepareTree.localTick d g))=
  UniformCacheRangeSelector.selections (UniformAllAxisSeedPreparation.radix n j)
   (UniformJointCacheAllocation.axis c n j).control L.length (UniformFourierAxisPrepareTree.localTick d g)
   (fun i=>L[i]?.getD (0,0)) nodes:=pair
 have geometry:=UniformFourierAxisWorkspace.axis_geometry c n j
 have nat:T≤(UniformFourierAxisWorkspace.axis c n j).rawRows:=by omega
 have keep:∀z,z<T→u.natHeap z=s.natHeap z:=by
  intro z hz
  rw[actual.bank]
  exact UniformCacheRangeSelector.writeSelections_low _ _ _ _ _ (hz.trans_le readNat)
 refine ⟨?_,?_,?_⟩
 · apply UniformActualCalendarSelectionBank.of_pairs eq
   intro i
   rw[actual.bank]
   simpa only[Nat.zero_add] using UniformGlobalCalendarSelector.writeSelections_get
    (UniformFourierAxisWorkspace.axis c n j).selected 0
    (UniformCacheRangeSelector.selections (UniformAllAxisSeedPreparation.radix n j)
     (UniformJointCacheAllocation.axis c n j).control L.length (UniformFourierAxisPrepareTree.localTick d g)
     (fun i=>L[i]?.getD (0,0)) nodes) s.natHeap i
 · intro e he
   exact cached_mono ((bundle.cached _ e he).transfer keep (fun z _=>congrFun actual.scalarHeap z)) scalar nat
 · have lengths:=congrArg List.length eq
   simpa only[UniformActualCalendarSelectionBank.pairs,List.length_map,UniformFourierAxisPrepareTree.count] using lengths

end
end ExactFourierCircuits.UniformFourierAxisTreeRegistryFacts

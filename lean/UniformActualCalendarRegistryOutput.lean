import UniformActualCalendarRegistryActual

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRegistry
open UniformMachine UniformGlobalCalendarDispatch
noncomputable section

lemma Bundle.selections {r O T B control L nodes s u tick A}
 (b:Bundle r O T B (control+3*r+4) L nodes s)
 (result:UniformCacheRangeSelector.Result r control L.length tick A
  (fun i=>L[i]?.getD (0,0)) nodes s u):Selections A 0 (b.events tick) u:=by
 apply UniformActualCalendarSelectionBank.of_pairs (b.pairs tick)
 exact result.bank

lemma Bundle.cached_after_selector {r O T B D L nodes s u tick}
 (b:Bundle r O T B D L nodes s)(natKeep:∀z,z<T→u.natHeap z=s.natHeap z)
 (scalarKeep:∀z,z<O→u.scalarHeap z=s.scalarHeap z):
 ∀e∈b.events tick,CachedEvent r O T B e u:=by
 intro e member
 exact (b.cached tick e member).transfer natKeep scalarKeep

end
end ExactFourierCircuits.UniformActualCalendarRegistry

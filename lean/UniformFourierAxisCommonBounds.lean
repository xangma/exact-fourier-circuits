import UniformFourierAxisCommonResult
import UniformFinalAxisCacheSource
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisCommonBounds
open UniformMachine UniformJointAllocation UniformJointCacheAllocation UniformAllAxisSeedPreparation
open UniformFourierAxisCommonResult UniformFourierAxisCanonicalEvents
noncomputable section

lemma records_count(c:Constants)(n:ℕ)(j:Fin (ell n)):
 (UniformFinalAxisCacheBundle.records c n j).length=UniformAxisCacheForestEntry.rectangleCount c n j:=
 UniformActualCalendarRectangleRegistry.entries_length n (UniformAxisCacheCanonicalRequests.canonical c n j)

lemma actual_tree_length{c:Constants}{n:ℕ}{hn:0<n}{j:Fin (ell n)}{s:State}
 (cache:UniformAxisCacheContents.Contents c n hn j s)(tick:ℕ):
 ((UniformFinalAxisCacheBundle.actual c n hn j cache).events tick).length≤UniformJointCacheExtent.capacity (radix n j):=by
 have pair:UniformActualCalendarSelectionBank.pairs
  ((UniformFinalAxisCacheBundle.actual c n hn j cache).events tick)=
  UniformCacheRangeSelector.selections (radix n j) (axis c n j).control
   (UniformFinalAxisCacheBundle.records c n j).length tick
   (fun i=>(UniformFinalAxisCacheBundle.records c n j)[i]?.getD (0,0)) (UniformFinalAxisCacheBundle.nodes c n j):=
  (UniformFinalAxisCacheBundle.actual c n hn j cache).pairs tick
 have length:=congrArg List.length pair
 simp only[UniformActualCalendarSelectionBank.pairs,List.length_map] at length
 rw[length]
 apply (UniformFourierAxisOperationalCases.selected_length _ _ _ _ _ _).trans
 rw[records_count]
 exact (UniformFinalAxisCacheSource.of_contents cache).countFit

lemma reference_tree_length{c:Constants}{n:ℕ}{hn:0<n}{j:Fin (ell n)}{s:State}
 (cache:UniformAxisCacheContents.Contents c n hn j s)(tick:ℕ):
 ((UniformFinalAxisCacheBundle.reference c n hn j cache).events tick).length≤UniformJointCacheExtent.capacity (radix n j):=by
 rw[←UniformFinalAxisCacheBundle.events_eq c n hn j cache tick]
 exact actual_tree_length cache tick

lemma one_le_capacity{n:ℕ}(hn:0<n)(j:Fin (ell n)):
 1≤UniformJointCacheExtent.capacity (radix n j):=by
 have positive:0<radix n j:=lt_of_lt_of_le (by decide:0<2) (UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn j)
 have square:1≤(radix n j)^2:=Nat.one_le_pow _ _ positive
 exact Nat.one_mul 1 ▸ Nat.mul_le_mul square (by omega:1≤UniformJointCacheExtent.slotCount (Nat.clog 2 (4*radix n j))+4)

lemma events_length{c:Constants}{n g:ℕ}{j:Fin (ell n)}(treeEvents:ℕ→List UniformGlobalCalendarDispatch.Event)
 (tree:∀tick,(treeEvents tick).length≤UniformJointCacheExtent.capacity (radix n j))
 (one:1≤UniformJointCacheExtent.capacity (radix n j)):
 (events c n g j treeEvents).length≤UniformJointCacheExtent.capacity (radix n j):=by
 classical
 unfold events eventsAt
 split_ifs
 · exact tree _
 · simpa only[UniformAxisBoundaryBindings.events,List.length_singleton] using one
 · simp

/-- Canonical clock-wide event count comes from the retained initial reference
bundle and the actual rectangle/leaf allocation, with no supplied count bound. -/
lemma reference_events_length{c:Constants}{n g:ℕ}{hn:0<n}{j:Fin (ell n)}{s:State}
 (cache:UniformAxisCacheContents.Contents c n hn j s):
 (events c n g j (UniformFinalAxisCacheBundle.reference c n hn j cache).events).length≤
 UniformJointCacheExtent.capacity (radix n j):=
 events_length _ (reference_tree_length cache) (one_le_capacity hn j)

lemma actual_events_length{c:Constants}{n g:ℕ}{hn:0<n}{j:Fin (ell n)}{s:State}
 (cache:UniformAxisCacheContents.Contents c n hn j s):
 (events c n g j (UniformFinalAxisCacheBundle.actual c n hn j cache).events).length≤
 UniformJointCacheExtent.capacity (radix n j):=
 events_length _ (actual_tree_length cache) (one_le_capacity hn j)
end
end ExactFourierCircuits.UniformFourierAxisCommonBounds

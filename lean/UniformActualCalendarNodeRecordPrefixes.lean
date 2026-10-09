import UniformActualCalendarBundleFactoryEvents
import UniformCalendarPreparationRecordPrefixes

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarNodeRecordPrefixes
noncomputable section
open UniformActualCalendarRegistry UniformLocalCacheTreeMachine UniformActualCalendarMacroOrder
open UniformCalendarActualAtoms UniformActualCalendarAtomRecords

variable (n:ℕ)(p:UniformDirectLeafForestData.Parameters)(visits:List Visit)(A:ℕ)
 {r O T B D:ℕ}{s:UniformMachine.State}
 (b:Bundle r O T B D (UniformActualCacheRectangleSource.entries n (UniformAxisCacheRequestSource.requests visits))
  (UniformDirectLeafForestRangeSource.nodeRanges p visits A) s)

lemma node_records:
 (List.ofFn (fun i:Fin (UniformDirectLeafForestRangeSource.nodeRanges p visits A).length=>(b.node i).scan)).map Scan.records=
 visits.map (fun q=>(directEvents q).flatMap (records n)):=by
 simp only[List.map_ofFn,Function.comp_def]
 apply List.ext_getElem
 · simp only[List.length_ofFn,List.length_map,UniformDirectLeafForestRangeSource.nodeRanges]
 · intro i hi hj
   have bound:i<visits.length:=by simpa only[List.length_map] using hj
   simp only[List.getElem_ofFn,List.getElem_map,Family.scan,
    UniformDirectLeafForestRangeSource.nodeRanges,List.get_eq_getElem]
   have eq:=forest_block n p visits A ⟨i,bound⟩
   exact eq

lemma node_prefix (i:Fin visits.length):
 (List.flatten (List.map Scan.records (List.take (nodeIndex p visits A i).val
  (List.ofFn (fun k:Fin (UniformDirectLeafForestRangeSource.nodeRanges p visits A).length=>(b.node k).scan))))).length =
 (((visits.take i.val).flatMap directEvents).flatMap (records n)).length:=by
 rw[List.map_take,node_records,←List.map_take]
 change ((visits.take i.val).flatMap (fun q=>(directEvents q).flatMap (records n))).length=_
 rw[←List.flatMap_assoc]

end
end ExactFourierCircuits.UniformActualCalendarNodeRecordPrefixes

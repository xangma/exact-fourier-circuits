import UniformActualCalendarNodeRecordPrefixes

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarNodeFineFactory
noncomputable section
open UniformMachine UniformJointAllocation UniformAllAxisSeedPreparation UniformLocalRequestPlan UniformLocalRequestGeometry
open UniformDirectLeafForestData UniformDirectLeafForestState UniformDirectLeafForestContents UniformLocalCacheTreeMachine
open UniformActualCalendarRegistry UniformActualCalendarMacroOrder UniformCalendarRefinementActive UniformCalendarActualAtoms

attribute [local irreducible] Nat.add Nat.mul of_actual

lemma operation_bound (n:ℕ)(visits:List Visit)(i:Fin visits.length)(j:Fin (directEvents (visits.get i)).length)
 (k:Fin (pieces n (preparationEvents visits) (UniformCalendarPreparationIndices.order visits (.inr ⟨i,j⟩))).length):
 k.val<UniformDirectLeafForestModel.operations visits[i]:=by
 have bound:=k.isLt
 simp only[pieces,UniformCalendarPreparationIndices.direct_descriptor,durations,List.length_map,
  UniformTransposeDescriptorMachine.leafRecords_length] at bound
 have stop:=UniformCalendarPreparationIndices.direct_leaf visits i j
 change UniformDirectLeafForestModel.leaf visits[i.val] at stop
 change k.val<UniformDirectLeafForestModel.operations visits[i.val]
 rw[UniformDirectLeafForestModel.operations,ite_eq_left stop]
 simpa only[UniformDirectLeafCacheLoopBoot.size,List.get_eq_getElem] using bound

variable {constants:Constants}{n:ℕ}{axisIndex:Fin (axisCount n)}{R N:ℕ}
 {p:Parameters}{visits:List Visit}{A:ℕ}{positive:2≤p.radix}{s:State}
 (g:Geometry constants n axisIndex (UniformAxisCacheRequestSource.requests visits) R N)
 (all:∀i (hi:i<(UniformAxisCacheRequestSource.requests visits).length),
  Complete constants n axisIndex (UniformAxisCacheRequestSource.requests visits) R N g i hi s)
 (forest:Contents p visits A positive s)(facts:Facts p visits)(hn:0<n)
 {O T:ℕ}(scalarRoom:3*slab constants n≤O)(natRoom:3*slab constants n≤T)
 (radixRoom:radix n axisIndex≤envelope constants n)(sameRadix:p.radix=radix n axisIndex)
 (entry:p.start.entry=p.start.permutation+3*p.radix+4)
 (pool:p.start.pool+9*p.radix*UniformDirectLeafForestModel.demand visits≤O)
 (nat:p.start.permutation+(3*p.radix+11)*UniformDirectLeafForestModel.demand visits≤T)


lemma make (i:Fin visits.length)(j:Fin (directEvents (visits.get i)).length)
 (k:Fin (pieces n (preparationEvents visits) (UniformCalendarPreparationIndices.order visits (.inr ⟨i,j⟩))).length)
 (elapsed:ℕ):
 (of_actual g all forest facts hn scalarRoom natRoom radixRoom sameRadix entry pool nat).scan.make
  (UniformCalendarRefinementActive.order n (preparationEvents visits)
   ⟨UniformCalendarPreparationIndices.order visits (.inr ⟨i,j⟩),k⟩).val elapsed=
 UniformActualCalendarDirectProduced.event
  (UniformActualCalendarForestRegistry.data (p:=p) (A:=A) forest i ⟨k.val,operation_bound n visits i j k⟩) elapsed:=by
 let b:=of_actual g all forest facts hn scalarRoom natRoom radixRoom sameRadix entry pool nat
 have bound:k.val<((UniformDirectLeafForestRangeSource.nodeRanges p visits A).get (nodeIndex p visits A i)).count:=by
  simpa only[UniformDirectLeafForestRangeSource.nodeRanges,nodeIndex,List.get_eq_getElem,List.getElem_ofFn] using operation_bound n visits i j k
 have head:=Bundle.scan_node_make b (nodeIndex p visits A i) k.val elapsed bound
 have pref:=UniformActualCalendarNodeRecordPrefixes.node_prefix n p visits A b i
 rw[pref] at head
 have actual:=actual_node_make g all forest facts hn scalarRoom natRoom radixRoom sameRadix entry pool nat
  i ⟨k.val,operation_bound n visits i j k⟩ elapsed
 rw[UniformCalendarPreparationRecordPrefixes.direct_fine]
 exact head.trans actual

end
end ExactFourierCircuits.UniformActualCalendarNodeFineFactory

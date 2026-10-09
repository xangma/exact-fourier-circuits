import UniformActualCalendarNodeFineFactory

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRectangleFineFactory
noncomputable section
open UniformMachine UniformJointAllocation UniformAllAxisSeedPreparation UniformLocalRequestPlan UniformLocalRequestGeometry
open UniformDirectLeafForestData UniformDirectLeafForestState UniformDirectLeafForestContents UniformLocalCacheTreeMachine
open UniformActualCalendarRegistry UniformActualCalendarMacroOrder UniformCalendarRefinementActive UniformCalendarActualAtoms

attribute [local irreducible] Nat.add Nat.mul of_actual

lemma slot_bound (n:ℕ)(visits:List Visit)(i:Fin (UniformAxisCacheRequestSource.requests visits).length)
 (j:Fin (pieces n (preparationEvents visits) (UniformCalendarPreparationIndices.order visits (.inl i))).length):
 j.val<slotCount n (UniformAxisCacheRequestSource.requests visits)[i].row:=by
 have bound:=j.isLt
 change j.val<(durations n ((preparationEvents visits).get
  (UniformCalendarPreparationIndices.order visits (.inl i))).event).length at bound
 rw[UniformCalendarPreparationIndices.rectangle_get] at bound
 simpa only[durations,List.length_replicate,List.get_eq_getElem,Fin.getElem_fin] using bound

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

lemma make (i:Fin (UniformAxisCacheRequestSource.requests visits).length)
 (j:Fin (pieces n (preparationEvents visits) (UniformCalendarPreparationIndices.order visits (.inl i))).length)
 (elapsed:ℕ):
 (of_actual g all forest facts hn scalarRoom natRoom radixRoom sameRadix entry pool nat).scan.make
  (UniformCalendarRefinementActive.order n (preparationEvents visits)
   ⟨UniformCalendarPreparationIndices.order visits (.inl i),j⟩).val elapsed=
 (UniformActualCalendarRectangleRegistry.data g all i.val i.isLt j.val (slot_bound n visits i j)).event
  _ _ _ _ _ _ _ _ elapsed:=by
 rw[UniformCalendarPreparationRecordPrefixes.rectangle_fine]
 exact actual_rectangle_make g all forest facts hn scalarRoom natRoom radixRoom sameRadix entry pool nat
  i.val i.isLt j.val elapsed (slot_bound n visits i j)

end
end ExactFourierCircuits.UniformActualCalendarRectangleFineFactory

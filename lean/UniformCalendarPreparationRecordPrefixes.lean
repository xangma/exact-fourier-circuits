import UniformCalendarFlattenPrefix

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarPreparationRecordPrefixes
noncomputable section
open UniformLocalCacheTreeMachine UniformAxisCacheRequestSource UniformActualCalendarMacroOrder
open UniformCalendarPreparationIndices UniformCalendarActualAtoms UniformActualCalendarAtomRecords
open UniformCalendarFlattenPrefix UniformLocalRequestPlan

lemma fine_val (n:ℕ)(E:List UniformLocalCacheTiming.TimedEvent)
 (i:Fin E.length)(j:Fin (UniformCalendarRefinementActive.pieces n E i).length):
 (UniformCalendarRefinementActive.order n E ⟨i,j⟩).val=
  ((E.take i.val).flatMap (records n)).length+j.val:=
 UniformCalendarFlattenIndices.order_val E (records n) i
  (finCongr (records_length n (E.get i)).symm j)

lemma rectangle (n:ℕ)(visits:List Visit)(i:Fin (requests visits).length):
 (((preparationEvents visits).take (order visits (.inl i)).val).flatMap (records n)).length=
 slotPrefix n (requests visits) i.val:=by
 rw[rectangle_val]
 change (((((requests visits).map rectangleEvent)++visits.flatMap directEvents).take i.val).flatMap (records n)).length=_
 rw[List.take_append_of_le_length (by simpa only[List.length_map] using i.isLt.le),←List.map_take,
  List.flatMap_map]
 have eq:(fun q:Request=>records n (rectangleEvent q))=UniformActualCacheRectangleSource.block n:=by
  funext q
  exact rectangle_records n q
 rw[eq]
 exact rectangle_prefix n (requests visits) i.val

lemma rectangle_fine (n:ℕ)(visits:List Visit)(i:Fin (requests visits).length)
 (j:Fin (UniformCalendarRefinementActive.pieces n (preparationEvents visits) (order visits (.inl i))).length):
 (UniformCalendarRefinementActive.order n (preparationEvents visits) ⟨order visits (.inl i),j⟩).val=
 slotPrefix n (requests visits) i.val+j.val:=by
 rw[fine_val,rectangle]

lemma direct (n:ℕ)(visits:List Visit)(i:Fin visits.length)(j:Fin (directEvents (visits.get i)).length):
 (((preparationEvents visits).take (order visits (.inr ⟨i,j⟩)).val).flatMap (records n)).length=
 (UniformActualCacheRectangleSource.entries n (requests visits)).length+
  (((visits.take i.val).flatMap directEvents).flatMap (records n)).length:=by
 have zero:=direct_zero visits i j
 have pos: (order visits (.inr ⟨i,j⟩)).val=
  ((requests visits).map rectangleEvent).length+
  (UniformCalendarFlattenIndices.order visits directEvents ⟨i,j⟩).val:=rfl
 rw[pos]
 change (((((requests visits).map rectangleEvent)++visits.flatMap directEvents).take
  (((requests visits).map rectangleEvent).length+
   (UniformCalendarFlattenIndices.order visits directEvents ⟨i,j⟩).val)).flatMap (records n)).length=_
 rw[List.take_length_add_append,UniformCalendarFlattenPrefix.take_order,List.flatMap_append,List.length_append,
  zero,List.take_zero,List.append_nil,List.flatMap_map]
 have eq:(fun q:Request=>records n (rectangleEvent q))=UniformActualCacheRectangleSource.block n:=by
  funext q
  exact rectangle_records n q
 rw[eq]
 rfl

lemma direct_fine (n:ℕ)(visits:List Visit)(i:Fin visits.length)(j:Fin (directEvents (visits.get i)).length)
 (k:Fin (UniformCalendarRefinementActive.pieces n (preparationEvents visits) (order visits (.inr ⟨i,j⟩))).length):
 (UniformCalendarRefinementActive.order n (preparationEvents visits) ⟨order visits (.inr ⟨i,j⟩),k⟩).val=
 (UniformActualCacheRectangleSource.entries n (requests visits)).length+
  (((visits.take i.val).flatMap directEvents).flatMap (records n)).length+k.val:=by
 rw[fine_val,direct,Nat.add_assoc]

end
end ExactFourierCircuits.UniformCalendarPreparationRecordPrefixes

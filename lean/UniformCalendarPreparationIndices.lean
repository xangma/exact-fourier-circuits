import UniformActualCalendarPhysicalRefinement

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarPreparationIndices
noncomputable section
open UniformLocalCacheTreeMachine UniformAxisCacheRequestSource UniformActualCalendarMacroOrder
open UniformCalendarFlattenIndices UniformLocalCacheTiming

abbrev Index (visits:List Visit):Type:=
 Fin (requests visits).length ⊕ (Σi:Fin visits.length,Fin (directEvents (visits.get i)).length)

def order (visits:List Visit):Index visits≃Fin (preparationEvents visits).length:=
 (Equiv.sumCongr (finCongr (List.length_map rectangleEvent).symm)
  (UniformCalendarFlattenIndices.order visits directEvents)).trans
  (finSumFinEquiv.trans (finCongr List.length_append.symm))

lemma rectangle_val (visits:List Visit)(i:Fin (requests visits).length):
 (order visits (.inl i)).val=i.val:=rfl

lemma direct_val (visits:List Visit)(i:Fin visits.length)(j:Fin (directEvents (visits.get i)).length):
 (order visits (.inr ⟨i,j⟩)).val=(requests visits).length+
  ((visits.take i.val).flatMap directEvents).length+j.val:=by
 change ((requests visits).map rectangleEvent).length+
  (UniformCalendarFlattenIndices.order visits directEvents ⟨i,j⟩).val=_
 rw[List.length_map,UniformCalendarFlattenIndices.order_val,Nat.add_assoc]

lemma rectangle_get (visits:List Visit)(i:Fin (requests visits).length):
 (preparationEvents visits).get (order visits (.inl i))=rectangleEvent ((requests visits).get i):=by
 change (((requests visits).map rectangleEvent)++visits.flatMap directEvents)[i.val]=_
 rw[List.getElem_append_left (by simpa only[List.length_map] using i.isLt),List.getElem_map]
 rfl

lemma direct_get (visits:List Visit)(i:Fin visits.length)(j:Fin (directEvents (visits.get i)).length):
 (preparationEvents visits).get (order visits (.inr ⟨i,j⟩))=(directEvents (visits.get i)).get j:=by
 have bound:((requests visits).map rectangleEvent).length+
  (UniformCalendarFlattenIndices.order visits directEvents ⟨i,j⟩).val<
  (((requests visits).map rectangleEvent)++visits.flatMap directEvents).length:=by
  rw[List.length_append]
  exact Nat.add_lt_add_left (UniformCalendarFlattenIndices.order visits directEvents ⟨i,j⟩).isLt _
 change (((requests visits).map rectangleEvent)++visits.flatMap directEvents)[((requests visits).map rectangleEvent).length+
   (UniformCalendarFlattenIndices.order visits directEvents ⟨i,j⟩).val]'bound=_
 rw[List.getElem_append_right (by omega)]
 simp only[Nat.add_sub_cancel_left]
 exact UniformCalendarFlattenIndices.get_order visits directEvents i j

lemma direct_leaf (visits:List Visit)(i:Fin visits.length)(j:Fin (directEvents (visits.get i)).length):
 UniformDirectLeafForestModel.leaf (visits.get i):=by
 by_contra no
 change ¬((visits.get i).task.width<2 ∨UniformWorkspacePlanner.selected (visits.get i).task.width=0) at no
 have bound:=j.isLt
 simp only[directEvents,ite_eq_right no,List.length_nil] at bound
 omega

lemma direct_zero (visits:List Visit)(i:Fin visits.length)(j:Fin (directEvents (visits.get i)).length):j.val=0:=by
 have stop:=direct_leaf visits i j
 change (visits.get i).task.width<2 ∨UniformWorkspacePlanner.selected (visits.get i).task.width=0 at stop
 have bound:=j.isLt
 simp only[directEvents,ite_eq_left stop,List.length_singleton] at bound
 omega

lemma direct_descriptor (visits:List Visit)(i:Fin visits.length)(j:Fin (directEvents (visits.get i)).length):
 (preparationEvents visits).get (order visits (.inr ⟨i,j⟩))=
 ⟨0,.direct (visits.get i).task.width (visits.get i).task.offset⟩:=by
 rw[direct_get]
 have stop:=direct_leaf visits i j
 change (visits.get i).task.width<2 ∨UniformWorkspacePlanner.selected (visits.get i).task.width=0 at stop
 have get_singleton {α:Type}(L:List α)(a:α)(eq:L=[a])(i:Fin L.length):L.get i=a:=by
  subst L
  exact List.getElem_singleton _
 exact get_singleton _ _ (ite_eq_left stop) j

end
end ExactFourierCircuits.UniformCalendarPreparationIndices

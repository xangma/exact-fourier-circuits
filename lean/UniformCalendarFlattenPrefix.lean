import UniformCalendarPreparationIndices

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarFlattenPrefix
noncomputable section
open UniformCalendarFlattenIndices

lemma take_order {α β:Type}(xs:List α)(f:α→List β)(i:Fin xs.length)(j:Fin (f (xs.get i)).length):
 (xs.flatMap f).take (UniformCalendarFlattenIndices.order xs f ⟨i,j⟩).val=
  (xs.take i.val).flatMap f++(f (xs.get i)).take j.val:=by
 have split:xs=xs.take i.val++xs.get i::xs.drop (i.val+1):=by
  change xs=xs.take i.val++xs[i.val]::xs.drop (i.val+1)
  rw[←List.drop_eq_getElem_cons i.isLt]
  exact (List.take_append_drop i.val xs).symm
 have expanded:xs.flatMap f=(xs.take i.val).flatMap f++
  (f (xs.get i)++(xs.drop (i.val+1)).flatMap f):=by
  calc
   xs.flatMap f=(xs.take i.val++xs.get i::xs.drop (i.val+1)).flatMap f:=congrArg _ split
   _=_:=by simp only[List.flatMap_append,List.flatMap_cons]
 rw[UniformCalendarFlattenIndices.order_val,expanded,List.take_length_add_append,
  List.take_append_of_le_length (Nat.le_of_lt j.isLt)]

open UniformLocalRequestPlan
lemma rectangle_prefix (n:ℕ)(qs:List Request)(i:ℕ):
 ((qs.take i).flatMap (UniformActualCacheRectangleSource.block n)).length=slotPrefix n qs i:=by
 induction qs generalizing i with
 | nil=>cases i <;>rfl
 | cons q qs ih=>
  cases i with
  | zero=>rfl
  | succ i=>
   simp only[List.take_succ_cons,List.flatMap_cons,List.length_append,
    UniformActualCacheRectangleSource.block_length,slotPrefix,ih]

end
end ExactFourierCircuits.UniformCalendarFlattenPrefix

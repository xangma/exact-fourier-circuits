import UniformCalendarPermutationActive
import UniformCalendarOrderedCalls

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarFlattenIndices
noncomputable section

variable {α β : Type}
def order (xs:List α)(f:α→List β):
 (Σi:Fin xs.length,Fin (f (xs.get i)).length)≃Fin (xs.flatMap f).length:=
 finSigmaFinEquiv.trans (finCongr (by
  rw[List.length_flatMap,UniformCalendarOrderedCalls.sum_get]))

lemma order_val (xs:List α)(f:α→List β)(i:Fin xs.length)(j:Fin (f (xs.get i)).length):
 (order xs f ⟨i,j⟩).val=((xs.take i.val).flatMap f).length+j.val:=by
 change (@finSigmaFinEquiv xs.length (fun i=>(f (xs.get i)).length) ⟨i,j⟩).val=_
 rw[finSigmaFinEquiv_apply,UniformCalendarOrderedCalls.prefix_sum xs (fun a=>(f a).length) i,List.length_flatMap]

lemma get_order (xs:List α)(f:α→List β)(i:Fin xs.length)(j:Fin (f (xs.get i)).length):
 (xs.flatMap f).get (order xs f ⟨i,j⟩)=(f (xs.get i)).get j:=by
 have split:xs=xs.take i.val++xs.get i::xs.drop (i.val+1):=by
  change xs=xs.take i.val++xs[i.val]::xs.drop (i.val+1)
  rw[←List.drop_eq_getElem_cons i.isLt]
  exact (List.take_append_drop i.val xs).symm
 have expanded:xs.flatMap f=(xs.take i.val).flatMap f++
  (f (xs.get i)++(xs.drop (i.val+1)).flatMap f):=by
  calc
   xs.flatMap f=(xs.take i.val++xs.get i::xs.drop (i.val+1)).flatMap f:=congrArg _ split
   _=_:=by simp only[List.flatMap_append,List.flatMap_cons]
 simp only[List.get_eq_getElem,order_val]
 rw[List.getElem_of_eq expanded,List.getElem_append_right (by omega)]
 simp only[Nat.add_sub_cancel_left]
 rw[List.getElem_append_left j.isLt]
 rfl

end
end ExactFourierCircuits.UniformCalendarFlattenIndices

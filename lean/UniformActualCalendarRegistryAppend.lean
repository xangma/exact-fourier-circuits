import UniformActualCalendarRegistryFamily

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRegistry
open UniformMachine UniformGlobalCalendarDispatch
noncomputable section

def Family.nil (r O T B D stride : ℕ) (s : State) : Family r O T B D stride [] s where
 entry:=fun j=>Fin.elim0 j

def Family.append {r O T B D stride xs ys s} (a : Family r O T B D stride xs s)
 (b : Family r O T B (D+stride*xs.length) stride ys s) : Family r O T B D stride (xs++ys) s where
 entry:=fun j=>by
  by_cases low:j.val<xs.length
  · exact Produced.cast (a.entry ⟨j.val,low⟩) rfl rfl
     (by simp only[List.get_eq_getElem,List.getElem_append_left low])
     (by simp only[List.get_eq_getElem,List.getElem_append_left low])
  · have high:xs.length≤j.val:=by omega
    have bound:j.val-xs.length<ys.length:=by have:=j.isLt;simp only[List.length_append] at this;omega
    apply Produced.cast (b.entry ⟨j.val-xs.length,bound⟩) rfl
    · change D+stride*xs.length+stride*(j.val-xs.length)=D+stride*j.val
      rw[Nat.add_assoc,←Nat.mul_add,show xs.length+(j.val-xs.length)=j.val by omega]
    · simp only[List.get_eq_getElem,List.getElem_append_right high]
    · simp only[List.get_eq_getElem,List.getElem_append_right high]

end
end ExactFourierCircuits.UniformActualCalendarRegistry

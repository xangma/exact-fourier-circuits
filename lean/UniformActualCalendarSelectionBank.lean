import UniformActualCalendarDirectPolicy

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarSelectionBank
open UniformMachine UniformGlobalCalendarDispatch

def pairs (es : List Event) : List (ℕ×ℕ):=
 es.map (fun e=>(e.descriptor.address,e.descriptor.elapsed))

/-- Exact physical selector cells imply the dispatcher's recursively indexed
Selections predicate, without supplying that predicate to the selector. -/
theorem of_cells {A used : ℕ} {es : List Event} {s : State}
 (bank : ∀i:Fin es.length,
  s.natHeap (A+2*(used+i.val))=some (es.get i).descriptor.address ∧
  s.natHeap (A+2*(used+i.val)+1)=some (es.get i).descriptor.elapsed) :
 Selections A used es s:=by
 induction es generalizing used with
 | nil=>trivial
 | cons e es ih=>
   have head:=bank ⟨0,by simp⟩
   refine ⟨?_,?_⟩
   · simpa only[List.get_eq_getElem,Nat.add_zero,List.getElem_cons_zero,Selected] using head
   · apply ih
     intro i
     have tail:=bank i.succ
     simpa only[List.get_eq_getElem,List.getElem_cons_succ,Fin.val_succ,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tail

/-- Applies directly to the actual range-selector Result.bank output. -/
theorem of_pairs {A : ℕ} {es : List Event} {qs : List (ℕ×ℕ)} {s : State}
 (eq : pairs es=qs)
 (bank : ∀i:Fin qs.length,s.natHeap (A+2*i.val)=some (qs.get i).1 ∧
  s.natHeap (A+2*i.val+1)=some (qs.get i).2) : Selections A 0 es s:=by
 subst qs
 apply of_cells
 intro i
 have bound:i.val<(pairs es).length:=by simpa only[pairs,List.length_map] using i.isLt
 simpa only[pairs,List.get_eq_getElem,List.getElem_map,Nat.zero_add] using bank ⟨i.val,bound⟩

end ExactFourierCircuits.UniformActualCalendarSelectionBank

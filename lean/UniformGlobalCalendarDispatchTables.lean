import UniformGlobalCalendarDispatchWhole

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalCalendarDispatch
open UniformMachine
noncomputable section

def eventRows (r : ℕ) (e : Event) : List (ℕ×ℕ):=match e.phase with
 | .diagonal _=>[]
 | .kernel=>List.ofFn (fun i:Fin (r-e.descriptor.widthCount)=>e.records i.val)
def allRows (r : ℕ) (es : List Event) : List (ℕ×ℕ):=es.flatMap (eventRows r)

lemma eventRows_length (r : ℕ) (e : Event) : (eventRows r e).length=callCount r e:=by
 cases phase:e.phase <;> simp [eventRows,phase,callCount,phaseCalls]
lemma allRows_cons (r : ℕ) (e : Event) (es : List Event) :
 allRows r (e::es)=eventRows r e++allRows r es:=rfl

lemma allRows_length (r : ℕ) (es : List Event) : (allRows r es).length=callTotal r es:=by
 induction es with
 | nil=>rfl
 | cons e es ih=>simp only [allRows_cons,List.length_append,eventRows_length,ih,callTotal_cons]

def CellRow (heap : ℕ→Option ℕ) (a : ℕ) (row : ℕ×ℕ) : Prop:=
 heap a=some row.1∧heap (a+1)=some row.2∧heap (a+2)=some 1

lemma foldRows_before (r T used : ℕ) (es : List Event) (heap : ℕ→Option ℕ) (z : ℕ)
 (before : z<T+3*used) : foldRows r T used es heap z=heap z:=by
 induction es generalizing used heap with
 | nil=>rfl
 | cons e es ih=>
   rw [foldRows,ih (used+callCount r e) _ (by omega)]
   cases phase:e.phase with
   | diagonal lane=>simp only [rowAction]
   | kernel=>exact UniformGlobalCalendarUnionRows.writeRows_low T used e.records 0 (r-e.descriptor.widthCount) heap z (by omega)

lemma rowAction_get (r T used : ℕ) (e : Event) (heap : ℕ→Option ℕ) (i : ℕ)
 (index : i<(eventRows r e).length) :
 CellRow (rowAction T used (r-e.descriptor.widthCount) e.phase e.records heap)
  (T+3*(used+i)) ((eventRows r e)[i]) :=by
 cases phase:e.phase with
 | diagonal lane=>simp only [eventRows,phase,List.length_nil] at index;omega
 | kernel=>
   simp only [eventRows,phase,List.length_ofFn] at index
   simpa only [rowAction,phase,eventRows,List.getElem_ofFn,CellRow] using
    UniformGlobalCalendarUnionRows.writeRows_get T used e.records 0 (r-e.descriptor.widthCount) heap i (by omega) (by omega)

/-- Every ordered union row printed by the actual selected fold has both
source endpoints and literal coefficient1, in selection order. -/
theorem foldRows_table (r T used : ℕ) (es : List Event) (heap : ℕ→Option ℕ) (i : ℕ)
 (index : i<(allRows r es).length) :
 CellRow (foldRows r T used es heap) (T+3*(used+i)) ((allRows r es)[i]) :=by
 induction es generalizing used heap i with
 | nil=>simp only [allRows,List.flatMap_nil,List.length_nil] at index;omega
 | cons e es ih=>
   change i<(eventRows r e++allRows r es).length at index
   change CellRow (foldRows r T (used+callCount r e) es
     (rowAction T used (r-e.descriptor.widthCount) e.phase e.records heap))
    (T+3*(used+i)) ((eventRows r e++allRows r es)[i])
   by_cases first:i<(eventRows r e).length
   · rw [List.getElem_append_left first]
     have cap:i<callCount r e:=by rwa [eventRows_length] at first
     simp only [CellRow]
     rw [foldRows_before r T (used+callCount r e) es _ _ (by omega),
      foldRows_before r T (used+callCount r e) es _ _ (by omega),
      foldRows_before r T (used+callCount r e) es _ _ (by omega)]
     exact rowAction_get r T used e heap i first
   · have after:(eventRows r e).length ≤ i:=by omega
     rw [List.getElem_append_right after]
     have tailIndex:i-(eventRows r e).length<(allRows r es).length:=by rw [List.length_append] at index;omega
     have result:=ih (used+callCount r e) (rowAction T used (r-e.descriptor.widthCount) e.phase e.records heap)
      (i-(eventRows r e).length) tailIndex
     have address:used+i=(used+callCount r e)+(i-(eventRows r e).length):=by rw [eventRows_length] at after ⊢;omega
     simpa only [address] using result

end
end ExactFourierCircuits.UniformGlobalCalendarDispatch

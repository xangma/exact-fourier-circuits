import UniformCalendarCallReindex

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarOrderedCalls
noncomputable section
open UniformGlobalCalendarDispatch

lemma sum_get {α : Type} (xs : List α) (f : α → ℕ) :
    (xs.map f).sum = ∑ i : Fin xs.length, f (xs.get i) := by
  calc
    (xs.map f).sum = (List.ofFn (fun i => f (xs.get i))).sum := by
      rw [List.ofFn_comp', List.ofFn_get]
    _ = _ := List.sum_ofFn

lemma prefix_get {α : Type} (xs : List α) (i : Fin xs.length) :
    List.ofFn (fun j : Fin i.val => xs.get (Fin.castLE i.isLt.le j)) = xs.take i.val := by
  apply List.ext_getElem
  · simp
  · intro j h₁ h₂
    simp only [List.getElem_ofFn, List.get_eq_getElem, List.getElem_take]
    rfl

lemma prefix_sum {α : Type} (xs : List α) (f : α → ℕ) (i : Fin xs.length) :
    ∑ j : Fin i.val, f (xs.get (Fin.castLE i.isLt.le j)) = ((xs.take i.val).map f).sum := by
  rw [← prefix_get xs i, List.map_ofFn, List.sum_ofFn]
  rfl

/-- The actual flatMap order: event order first, then that event's stored rows. -/
def order (r : ℕ) (es : List Event) :
    (Σ i : Fin es.length, Fin (callCount r (es.get i))) ≃ Fin (callTotal r es) :=
  finSigmaFinEquiv.trans (finCongr (sum_get es (callCount r)).symm)

@[simp] lemma order_val (r : ℕ) (es : List Event)
    (i : Fin es.length) (j : Fin (callCount r (es.get i))) :
    (order r es ⟨i,j⟩).val = callTotal r (es.take i.val) + j.val := by
  change (@finSigmaFinEquiv es.length (fun i => callCount r (es.get i)) ⟨i,j⟩).val = _
  rw [finSigmaFinEquiv_apply, prefix_sum]
  rfl

lemma allRows_get_order (r : ℕ) (es : List Event)
    (i : Fin es.length) (j : Fin (callCount r (es.get i))) :
    (allRows r es).get ⟨(order r es ⟨i,j⟩).val,
      by rw [allRows_length]; exact (order r es ⟨i,j⟩).isLt⟩ =
    (eventRows r (es.get i)).get ⟨j.val,by rw [eventRows_length]; exact j.isLt⟩ := by
  have split : es = es.take i.val ++ es.get i :: es.drop (i.val+1) := by
    change es = es.take i.val ++ es[i.val] :: es.drop (i.val+1)
    rw [← List.drop_eq_getElem_cons i.isLt]
    exact (List.take_append_drop i.val es).symm
  have rows : allRows r es = allRows r (es.take i.val) ++
      (eventRows r (es.get i) ++ allRows r (es.drop (i.val+1))) := by
    calc
      allRows r es = allRows r (es.take i.val ++ es.get i :: es.drop (i.val+1)) := congrArg _ split
      _ = _ := by simp only [allRows, List.flatMap_append, List.flatMap_cons]
  simp only [List.get_eq_getElem, order_val]
  rw [List.getElem_of_eq rows]
  rw [List.getElem_append_right (by rw [allRows_length]; omega)]
  simp only [allRows_length, Nat.add_sub_cancel_left]
  rw [List.getElem_append_left (by rw [eventRows_length]; exact j.isLt)]
  rfl

lemma eventRows_get (r : ℕ) (e : Event) (i : Fin (callCount r e)) :
    (eventRows r e).get ⟨i.val,by rw [eventRows_length]; exact i.isLt⟩ = e.records i.val := by
  cases phase : e.phase with
  | diagonal lane =>
    have h : i.val < 0 := by simpa [callCount, phase, phaseCalls] using i.isLt
    omega
  | kernel => simp [eventRows, phase]

lemma allRows_get_records (r : ℕ) (es : List Event)
    (i : Fin es.length) (j : Fin (callCount r (es.get i))) :
    (allRows r es).get ⟨(order r es ⟨i,j⟩).val,
      by rw [allRows_length]; exact (order r es ⟨i,j⟩).isLt⟩ = (es.get i).records j.val := by
  rw [allRows_get_order, eventRows_get]

end
end ExactFourierCircuits.UniformCalendarOrderedCalls

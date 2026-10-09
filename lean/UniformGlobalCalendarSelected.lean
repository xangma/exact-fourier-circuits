import UniformGlobalCalendarSelectorLoop

set_option autoImplicit false

namespace ExactFourierCircuits.UniformGlobalCalendarSelector
noncomputable section

/-- Every active ordinal is retained, including concurrent entries from distinct subtrees. -/
theorem mem_selected (D stride tick : ℕ) (records : ℕ → ℕ × ℕ)
    (j fuel : ℕ) (q : ℕ × ℕ) :
    q ∈ selected D stride tick records j fuel ↔
      ∃ k, j ≤ k ∧ k < j + fuel ∧ active tick (records k).1 (records k).2 ∧
        q = (D + stride * k, tick - (records k).1) := by
  induction fuel generalizing j with
  | zero => simp only [selected,List.not_mem_nil,Nat.add_zero]; constructor <;> intro h
            · contradiction
            · obtain ⟨k,lo,hi,_⟩ := h; omega
  | succ fuel ih =>
    by_cases enabled : active tick (records j).1 (records j).2
    · rw [selected,ite_eq_left enabled,List.mem_cons,ih]
      constructor
      · rintro (eq | ⟨k,lo,hi,on,eq⟩)
        · exact ⟨j,le_rfl,by omega,enabled,eq⟩
        · exact ⟨k,by omega,by omega,on,eq⟩
      · rintro ⟨k,lo,hi,on,eq⟩
        by_cases same : k = j
        · subst k; exact Or.inl eq
        · exact Or.inr ⟨k,by omega,by omega,on,eq⟩
    · rw [selected,ite_eq_right enabled,ih]
      constructor
      · rintro ⟨k,lo,hi,on,eq⟩
        exact ⟨k,by omega,by omega,on,eq⟩
      · rintro ⟨k,lo,hi,on,eq⟩
        have ne : k ≠ j := by intro h; subst k; exact enabled on
        exact ⟨k,by omega,by omega,on,eq⟩

lemma writeSelections_low (O used : ℕ) (qs : List (ℕ × ℕ)) (heap : ℕ → Option ℕ)
    (a : ℕ) (ha : a < O + 2 * used) : writeSelections O used qs heap a = heap a := by
  induction qs generalizing used heap with
  | nil => rfl
  | cons q qs ih =>
    rw [writeSelections,ih _ _ (by omega)]
    simp (disch := omega) [storeSelection]

/-- The fresh output bank contains the selected address/phase pairs in order. -/
theorem writeSelections_get (O used : ℕ) (qs : List (ℕ × ℕ)) (heap : ℕ → Option ℕ)
    (i : Fin qs.length) :
    writeSelections O used qs heap (O + 2 * (used + i.val)) = some (qs.get i).1 ∧
    writeSelections O used qs heap (O + 2 * (used + i.val) + 1) = some (qs.get i).2 := by
  induction qs generalizing used heap with
  | nil => exact Fin.elim0 i
  | cons q qs ih =>
    by_cases zero : i.val = 0
    · have eq : i = 0 := Fin.ext zero
      subst i
      change writeSelections O (used + 1) qs (storeSelection O used q.1 q.2 heap)
        (O + 2 * (used + 0)) = some q.1 ∧
        writeSelections O (used + 1) qs (storeSelection O used q.1 q.2 heap)
        (O + 2 * (used + 0) + 1) = some q.2
      rw [writeSelections_low _ _ _ _ _ (by omega),writeSelections_low _ _ _ _ _ (by omega)]
      simp (disch := omega) [storeSelection]
    · let k : Fin qs.length := ⟨i.val - 1, by have := i.isLt; simp only [List.length_cons] at this; omega⟩
      have eq : i = k.succ := Fin.ext (by simp [k];omega)
      have getEq : (q :: qs).get i = qs.get k := by rw [eq]; rfl
      have valEq : i.val = k.val + 1 := by simp [k]; omega
      simpa only [writeSelections,getEq,valEq,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
        using ih (used + 1) (storeSelection O used q.1 q.2 heap) k

end
end ExactFourierCircuits.UniformGlobalCalendarSelector

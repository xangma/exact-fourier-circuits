import UniformLocalCacheSlotInvariant

set_option autoImplicit false
namespace ExactFourierCircuits.UniformReplaySlotIndex
noncomputable section
open UniformLocalCacheChronology UniformLocalReplayAssembly
open UniformLocalReplaySlotMachine (slots slots_length decodedSlot levelCount slots_all_phases)

lemma ofFn_val {α : Type} (n : ℕ) (f : ℕ → α) :
    List.ofFn (fun i : Fin n => f i.val) = (List.range n).map f := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp

lemma slots_ofFn (H : ℕ) (b e inv : Bool) :
    slots H b e inv = List.ofFn (fun i : Fin (levelCount H b*11) =>
      decodedSlot H b e inv (i.val/11) (i.val%11)) := by
  have base : slots H b e inv =
      (List.ofFn (fun d : Fin (levelCount H b) => List.ofFn (fun c : Fin 11 =>
        decodedSlot H b e inv d.val c.val))).flatten := by
    simp_rw [ofFn_val]
    rw [ofFn_val (levelCount H b) (fun d => (List.range 11).map (decodedSlot H b e inv d))]
    rfl
  rw [base, List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext d
  apply congrArg List.ofFn
  funext c
  have div : (d.val*11+c.val)/11=d.val := by have:=c.isLt; omega
  have mod : (d.val*11+c.val)%11=c.val := by have:=c.isLt; omega
  simp only [div, mod]

lemma slots_get (H : ℕ) (b e inv : Bool) (t : ℕ) (ht : t<11*levelCount H b) :
    (slots H b e inv).get ⟨t,by rw [slots_length]; exact ht⟩ =
      decodedSlot H b e inv (t/11) (t%11) := by
  simp only [List.get_eq_getElem]
  rw [List.getElem_of_eq (slots_ofFn H b e inv), List.getElem_ofFn]

def phaseSlots (H : ℕ) (p : Fin 6) : List Slot :=
  slots H (flags p).broadcast (flags p).enabled (flags p).inverse

def phases (H : ℕ) : List (List Slot) := List.ofFn (phaseSlots H)

lemma phases_flatten (H : ℕ) : (phases H).flatten = replaySlots H := by
  have h := slots_all_phases H
  simpa [phases, phaseSlots, List.ofFn_succ, flags] using h

lemma phase_length (H : ℕ) (p : Fin 6) : (phaseSlots H p).length = 11*levels H p :=
  slots_length H _ _ _

lemma prefix_length (H : ℕ) (p : Fin 6) :
    ((phases H).take p.val).flatten.length = 11*phasePrefix H p.val := by
  fin_cases p <;>
    simp [phases, phaseSlots, List.ofFn_succ, slots_length, flags, phasePrefix,
      levels, levelCount] <;> omega

lemma flatMap_get_offset {α β : Type} (xs : List α) (f : α → List β)
    (i : Fin xs.length) (j : Fin (f (xs.get i)).length) :
    (xs.flatMap f).get ⟨((xs.take i.val).flatMap f).length+j.val,by
      have split : xs = xs.take i.val ++ xs.get i :: xs.drop (i.val+1) := by
        change xs = xs.take i.val ++ xs[i.val] :: xs.drop (i.val+1)
        rw [← List.drop_eq_getElem_cons i.isLt]
        exact (List.take_append_drop i.val xs).symm
      have eq := congrArg (fun ys => (ys.flatMap f).length) split
      simp only [List.flatMap_append, List.flatMap_cons, List.length_append] at eq
      have := j.isLt
      omega⟩ = (f (xs.get i)).get j := by
  have split : xs = xs.take i.val ++ xs.get i :: xs.drop (i.val+1) := by
    change xs = xs.take i.val ++ xs[i.val] :: xs.drop (i.val+1)
    rw [← List.drop_eq_getElem_cons i.isLt]
    exact (List.take_append_drop i.val xs).symm
  have rows : xs.flatMap f = (xs.take i.val).flatMap f ++
      (f (xs.get i) ++ (xs.drop (i.val+1)).flatMap f) := by
    calc
      xs.flatMap f = (xs.take i.val ++ xs.get i :: xs.drop (i.val+1)).flatMap f := congrArg _ split
      _ = _ := by rw [List.flatMap_append, List.flatMap_cons]
  simp only [List.get_eq_getElem]
  rw [List.getElem_of_eq rows, List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem_append_left j.isLt]
  rfl

lemma replay_get_phase (H : ℕ) (p : Fin 6) (t : ℕ) (ht : t<11*levels H p) :
    (replaySlots H).get ⟨11*phasePrefix H p.val+t,by
      rw [replaySlots_length]
      have bound := prefix_mono H (show p.val+1≤6 by have:=p.isLt; omega)
      rw [prefix_next, prefix_total] at bound
      omega⟩ =
    decodedSlot H (flags p).broadcast (flags p).enabled (flags p).inverse (t/11) (t%11) := by
  let idx : Fin (phases H).length := ⟨p.val,by
    simpa only [phases, List.length_ofFn] using p.isLt⟩
  have item : (phases H).get idx = phaseSlots H p := by
    change (List.ofFn (phaseSlots H))[p.val] = _
    rw [List.getElem_ofFn]
  have h := flatMap_get_offset (phases H) id idx
    ⟨t,by change t < ((phases H).get idx).length; rw [item, phase_length]; exact ht⟩
  simp only [List.flatMap_id, id_eq] at h
  change (phases H).flatten.get ⟨((phases H).take p.val).flatten.length+t,_⟩ =
    ((phases H).get idx).get _ at h
  simp only [List.get_eq_getElem, prefix_length] at h
  rw [List.getElem_of_eq (phases_flatten H)] at h
  have item' : (phases H)[idx.val] = phaseSlots H p := item
  rw [List.getElem_of_eq item'] at h
  exact h.trans (slots_get H _ _ _ t ht)


end
end ExactFourierCircuits.UniformReplaySlotIndex

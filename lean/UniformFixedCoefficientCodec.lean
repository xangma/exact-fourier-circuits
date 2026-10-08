import UniformFixedNetwork

set_option autoImplicit false

/- The actual saving network uses five rational scalar values. This is a static
   metadata codec, not a RAM implementation of the saving network. -/
namespace ExactFourierCircuits.UniformFixedCoefficientCodec
open ScalarNetwork GateFrames FramedScheduleWords UniformFixedNetwork
noncomputable section

/-- Zero is included for complete physical rows, though events exclude it. -/
def Small (z : ℂ) : Prop :=
  z = -1 ∨ z = -1 / 2 ∨ z = 0 ∨ z = 1 / 2 ∨ z = 1

lemma small_zero : Small 0 := Or.inr (Or.inr (Or.inl rfl))
lemma small_one : Small 1 := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
lemma small_half : Small (1 / 2) := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
lemma small_neg_half : Small (-1 / 2) := Or.inr (Or.inl rfl)

lemma Small.neg {z : ℂ} (hz : Small z) : Small (-z) := by
  rcases hz with h | h | h | h | h
  · rw [h]; simpa using small_one
  · rw [h]; convert small_half using 1; ring
  · rw [h]; simpa using small_zero
  · rw [h]; convert small_neg_half using 1; ring
  · rw [h]; exact Or.inl rfl

variable {α : Type*} [DecidableEq α]

lemma coefficient_small (S T : Triple α) : Small (coefficient S T) := by
  have hb : (S.val ∩ T.val).card ≤ 3 :=
    (Finset.card_le_card Finset.inter_subset_left).trans_eq S.property
  unfold coefficient
  interval_cases hc : (S.val ∩ T.val).card <;> norm_num [Small]

lemma G_small (i : Option α) (T : Triple α) : Small (G i T) := by
  cases i with
  | none => exact small_one
  | some j => by_cases h : j ∈ T.val <;> simp [G,h,small_one,small_zero]

lemma R_small (S : Triple α) (i : Option α) : Small (R S i) := by
  cases i with
  | none => exact small_neg_half
  | some j =>
    by_cases h : j ∈ S.val
    · simpa only [R,Matrix.of_apply,h,ite_true] using small_half
    · simpa only [R,Matrix.of_apply,h,ite_false] using small_zero

lemma V_small (e : Edge α) (T : Triple α) : Small (V e T) := by
  by_cases h : e.val.2 = T <;> simp [V,h,small_one,small_zero]

lemma J_small (S : Triple α) (e : Edge α) : Small (J S e) := by
  by_cases h : e.val.1 = S
  · simpa [J,h] using (coefficient_small S e.val.2).neg
  · simp [J,h,small_zero]

lemma row_small {h : ℕ} (row : Fin 8) (a b : Role h) :
    Small (rowCoefficient row a b) := by
  fin_cases row <;> cases a <;> cases b <;>
    simp only [rowCoefficient] <;>
    first | exact small_zero | exact (J_small _ _).neg | exact (R_small _ _).neg |
      exact V_small _ _ | exact G_small _ _ | exact R_small _ _ | exact J_small _ _ |
      exact (G_small _ _).neg | exact (V_small _ _).neg

lemma reverse_row_small {h : ℕ} (row : Fin 8) (a b : Role h) :
    Small (reverseRowCoefficient row a b) := by
  fin_cases row <;> cases a <;> cases b <;>
    simp only [reverseRowCoefficient] <;>
    first | exact small_zero | exact (J_small _ _).neg | exact (R_small _ _).neg |
      exact V_small _ _ | exact G_small _ _ | exact R_small _ _ | exact J_small _ _ |
      exact (G_small _ _).neg | exact (V_small _ _).neg

/-- These five values can be made from prepared 0,1,2 by charged arithmetic. -/
def decode (k : Fin 5) : ℂ :=
  if k.val = 0 then -1 else if k.val = 1 then -1 / 2 else
  if k.val = 2 then 0 else if k.val = 3 then 1 / 2 else 1

def code (z : ℂ) : Fin 5 :=
  if z = -1 then 0 else if z = -1 / 2 then 1 else
  if z = 0 then 2 else if z = 1 / 2 then 3 else 4

lemma decode_code {z : ℂ} (hz : Small z) : decode (code z) = z := by
  rcases hz with h | h | h | h | h <;> rw [h] <;> norm_num [decode,code]

lemma code_round_trip (k : Fin 5) : code (decode k) = k := by
  fin_cases k <;> norm_num [decode,code]

lemma decode_small (k : Fin 5) : Small (decode k) := by
  fin_cases k <;> norm_num [decode,Small]

lemma decode_real (k : Fin 5) : (decode k).im = 0 := by
  fin_cases k <;> norm_num [decode]

variable {r n : ℕ}

def EventsSmall : ∀ {F G : Labels r n}, Schedule F G → Prop
  | _, _, .nil _ => True
  | _, _, .cons e s => Small e.coefficient ∧ EventsSmall s

lemma events_append {F G H : Labels r n} (s : Schedule F G) (t : Schedule G H)
    (hs : EventsSmall s) (ht : EventsSmall t) : EventsSmall (s.append t) := by
  induction s with
  | nil F => exact ht
  | cons e s ih => exact ⟨hs.1,ih t hs.2 ht⟩

variable {ι η : Type*} [Fintype ι] [Fintype η]
  {h : ℕ}

lemma constant_rows_small (d : GateFrames.Data ι η h)
    (e : ((ι × Fin h) × η) ≃ Fin n) (row : Fin 8)
    (L : List (TripleSchedule.RowEntry (h := h) row)) :
    EventsSmall (TripleSchedule.constantRowSchedule d e row L) := by
  induction L with
  | nil => trivial
  | cons f fs ih => exact ⟨row_small row _ _,ih⟩

lemma row_schedule_small (d : GateFrames.Data ι η h)
    (e : ((ι × Fin h) × η) ≃ Fin n) (row : Fin 8) :
    EventsSmall (TripleSchedule.rowSchedule d e row) := by
  unfold TripleSchedule.rowSchedule
  split
  · rename_i he
    exact False.elim (TripleSchedule.rowSupportList_ne_nil d.large row he)
  · exact ⟨row_small row _ _,constant_rows_small d e row _⟩

lemma local_schedule_small (d : GateFrames.Data ι η h)
    (e : ((ι × Fin h) × η) ≃ Fin n) :
    EventsSmall (TripleSchedule.localSchedule d e) := by
  unfold TripleSchedule.localSchedule
  repeat' apply events_append
  all_goals exact row_schedule_small d e _

lemma reverse_constant_rows_small (d : GateFrames.Data ι η h)
    (e : ((ι × Fin h) × η) ≃ Fin n) (row : Fin 8)
    (L : List (TripleSchedule.ReverseLocal.RowEntry (h := h) row)) :
    EventsSmall (TripleSchedule.ReverseLocal.constantRowSchedule d e row L) := by
  induction L with
  | nil => trivial
  | cons f fs ih => exact ⟨reverse_row_small row _ _,ih⟩

lemma reverse_row_schedule_small (d : GateFrames.Data ι η h)
    (e : ((ι × Fin h) × η) ≃ Fin n) (row : Fin 8) :
    EventsSmall (TripleSchedule.ReverseLocal.rowSchedule d e row) := by
  unfold TripleSchedule.ReverseLocal.rowSchedule
  split
  · rename_i he
    exact False.elim (TripleSchedule.ReverseLocal.rowSupportList_ne_nil d.large row he)
  · exact ⟨reverse_row_small row _ _,reverse_constant_rows_small d e row _⟩

lemma reverse_local_schedule_small (d : GateFrames.Data ι η h)
    (e : ((ι × Fin h) × η) ≃ Fin n) :
    EventsSmall (TripleSchedule.ReverseLocal.localSchedule d e) := by
  unfold TripleSchedule.ReverseLocal.localSchedule
  repeat' apply events_append
  all_goals exact reverse_row_schedule_small d e _

def MacroSmall : Macro r n → Prop
  | .edge _ _ _ _ => True
  | .shear _ _ _ z _ => Small z

def TapeSmall (L : List (Macro r n)) : Prop := ∀ a ∈ L, MacroSmall a

lemma tape_append (L K : List (Macro r n)) (hL : TapeSmall L) (hK : TapeSmall K) :
    TapeSmall (L ++ K) := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hL a ha
  · exact hK a ha

lemma edges_small {F G : Labels r n} (edges : ∀ i, NestedEdge (F i) (G i)) :
    TapeSmall (edgesTape edges) := by
  intro a ha
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
  trivial

lemma event_small {F G : Labels r n} (e : Event F G) (he : Small e.coefficient) :
    TapeSmall (eventTape e) := by
  apply tape_append _ _ (edges_small e.edges)
  intro a ha
  simpa [MacroSmall] using (List.mem_singleton.mp ha ▸ he)

lemma schedule_small {F G : Labels r n} (s : Schedule F G) (hs : EventsSmall s) :
    TapeSmall (scheduleTape s) := by
  induction s with
  | nil F => intro a ha; cases ha
  | cons e s ih => exact tape_append _ _ (event_small e hs.1) (ih hs.2)

lemma finish_small {F G H : Labels r n} (s : Schedule F G)
    (edges : ∀ i, NestedEdge (G i) (H i)) (hs : EventsSmall s) :
    TapeSmall (finishTape s edges) :=
  tape_append _ _ (schedule_small s hs) (edges_small edges)

lemma actual_block_small (h : ℕ) (hh : 7 ≤ h) (a : MasterBudget.Invocation h) :
    TapeSmall (finishTape (MasterBudget.actualBlock h hh a).schedule
      (MasterBudget.actualBlock h hh a).sinkEdges) := by
  unfold MasterBudget.actualBlock
  dsimp only
  by_cases hp : a.1 = 1
  · rw [ite_eq_left hp]; exact finish_small _ _ (reverse_local_schedule_small _ _)
  · rw [ite_eq_right hp]; exact finish_small _ _ (local_schedule_small _ _)

/-- Every shear in the actual fixed master chronology has a finite scalar code. -/
theorem fixed_block_small (a : MasterBudget.Invocation ExplicitSeedBudget.h) :
    TapeSmall (finishTape (fixedBlock a).schedule (fixedBlock a).sinkEdges) :=
  actual_block_small _ UniformFixedNetwork.hh a

/-- Static metadata has a finite scalar code, with no arbitrary complex field. -/
inductive EncodedMacro (r n : ℕ) where
  | edge (F G : Label n) (i : Fin r) (e : NestedEdge F G)
  | shear (d s : Fin r) (distinct : d ≠ s) (k : Fin 5) (nz : decode k ≠ 0)

def decodeMacro : EncodedMacro r n → Macro r n
  | .edge F G i e => .edge F G i e
  | .shear d s distinct k nz => .shear d s distinct (decode k) nz

def encodeMacro (a : Macro r n) (ha : MacroSmall a) : EncodedMacro r n := by
  cases a with
  | edge F G i e => exact .edge F G i e
  | shear d s distinct z nz =>
    exact .shear d s distinct (code z) (by rw [decode_code ha]; exact nz)

lemma decode_encodeMacro (a : Macro r n) (ha : MacroSmall a) :
    decodeMacro (encodeMacro a ha) = a := by
  cases a with
  | edge => rfl
  | shear d s h z nz => simp [encodeMacro,decodeMacro,decode_code ha]

def encodeTape (L : List (Macro r n)) (hL : TapeSmall L) : List (EncodedMacro r n) :=
  match L with
  | [] => []
  | a :: K => encodeMacro a (hL a (by simp)) ::
    encodeTape K (fun b hb => hL b (by simp [hb]))

lemma decode_encodeTape (L : List (Macro r n)) (hL : TapeSmall L) :
    (encodeTape L hL).map decodeMacro = L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    change decodeMacro (encodeMacro a _) :: (encodeTape L _).map decodeMacro = a :: L
    rw [decode_encodeMacro]
    exact congrArg (List.cons a) (ih (fun b hb => hL b (by simp [hb])))

/-- Every event code is real, so its conjugate needs no separate spectrum. -/
lemma encoded_shear_conjugate (k : Fin 5) : starRingEnd ℂ (decode k) = decode k := by
  fin_cases k <;> norm_num [decode,starRingEnd_apply]

/-- Encoding preserves the actual fixed block word and its chronology. -/
theorem encoded_fixed_block_compile (q : ℕ)
    (a : MasterBudget.Invocation ExplicitSeedBudget.h) :
    compileTape q ((encodeTape
      (finishTape (fixedBlock a).schedule (fixedBlock a).sinkEdges)
      (fixed_block_small a)).map decodeMacro) =
    compileTape q (finishTape (fixedBlock a).schedule (fixedBlock a).sinkEdges) := by
  rw [decode_encodeTape]

end
end ExactFourierCircuits.UniformFixedCoefficientCodec

import TripleInvocationFrames
import TerminalWords
set_option autoImplicit false
namespace ExactFourierCircuits.TripleStageAction
open BinaryFrames BinaryComplement BinaryTensor BinaryResiduals BinaryProjection FrameSpectrum
open GateFrames FramedScheduleWords TripleNetwork
noncomputable section
variable {h n : ℕ}
lemma label_exponent_bot (L : Label n) (hL : L.space = ⊥) : L.exponent = fun _ => 0 := by
  funext x
  have hp := frameProjection_mem_span L.vectors x
  rw [L.span, hL] at hp
  have hz : frameProjection L.vectors x = 0 := hp
  simp [Label.exponent, frameExponent, hz, weightModFour, weight]
lemma label_exponent_top (L : Label n) (hL : L.space = ⊤) : L.exponent = weightModFour := by
  funext x
  have hp := frameProjection_fixed_of_mem_span L.vectors L.orthonormal x
    (by rw [L.span, hL]; trivial)
  simp only [Label.exponent, frameExponent, hp]
lemma label_exponent_line (L : Label n) (u : Vec (Fin n)) (hu : dot u u = 1)
    (hL : L.space = line u) : L.exponent = lineExponent u := by
  funext x
  have hp : frameProjection L.vectors x = dot u x • u := by
    apply frameProjection_unique L.vectors L.orthonormal
    · rw [L.span, hL]
      exact (mem_line u _).mpr ⟨dot u x, rfl⟩
    · intro i
      have hi : L.vectors i ∈ line u := by rw [← hL]; exact (L.basis i).property
      obtain ⟨c, hc⟩ := (mem_line u _).mp hi
      rw [← hc, dot_smul_left, dot_smul_right, hu, mul_one, dot_smul_left]
  simp only [Label.exponent, frameExponent, hp, lineExponent]
lemma label_exponent_perp (L : Label n) (u : Vec (Fin n)) (hu : dot u u = 1)
    (hL : L.space = perp u) : L.exponent = perpExponent u := by
  funext x
  have hp : frameProjection L.vectors x = x + dot u x • u := by
    apply frameProjection_unique L.vectors L.orthonormal
    · rw [L.span, hL]
      change dot u (x + dot u x • u) = 0
      rw [dot_add_right, dot_smul_right, hu, mul_one]
      exact CharTwo.add_self_eq_zero _
    · intro i
      have hi : dot u (L.vectors i) = 0 := by
        have hi : L.vectors i ∈ perp u := by simpa only [hL, Label.vectors] using (L.basis i).property
        exact hi
      rw [dot_add_right, dot_smul_right, dot_comm (L.vectors i) u, hi, mul_zero, add_zero]
  simp only [Label.exponent, frameExponent, hp, perpExponent]
abbrev Aux (h : ℕ) := Σ p : Fin 3, Profile (Fin h) p × (ScalarNetwork.Edge (Fin h) ⊕ Option (Fin h))
abbrev Role (h : ℕ) := TripleCounting.Role (Fin h)
abbrev Arrays (h : ℕ) := Role h → Array (ι := Fin (h ^ 3))
def zeroLabel (n : ℕ) : Label n := labelOfBasis (hasONBasis_bot (ι := Fin n))
def fullLabel (n : ℕ) : Label n := labelOfBasis (hasONBasis_top (ι := Fin n))
def incoming (hh : 7 ≤ h) (p : Fin 3) : Role h → Label (h ^ 3)
  | .inl (b, d) =>
    let data := TripleInvocationFrames.invocationData p (TripleInvocationFrames.bankProfile p d) hh
    data.labels (TripleInvocationFrames.invocationAddressCoordinates p h) 0
      (if b = 0 then .x (d p) else .y (d p))
  | .inr a => if a.1 < p then fullLabel (h ^ 3) else zeroLabel (h ^ 3)
def outgoing (hh : 7 ≤ h) (p : Fin 3) : Role h → Label (h ^ 3)
  | .inl (b, d) =>
    let data := TripleInvocationFrames.invocationData p (TripleInvocationFrames.bankProfile p d) hh
    data.finalLabels (TripleInvocationFrames.invocationAddressCoordinates p h)
      (if b = 0 then .x (d p) else .y (d p))
  | .inr a => if a.1 ≤ p then fullLabel (h ^ 3) else zeroLabel (h ^ 3)
lemma consecutive_spaces (hh : 7 ≤ h) (p : Fin 2) (r : Role h) :
    (outgoing hh p.castSucc r).space = (incoming hh p.succ r).space := by
  cases r with
  | inl rd =>
    rcases rd with ⟨b, d⟩
    fin_cases b
    · exact (TripleInvocationFrames.consecutive_bank p d hh).1
    · exact (TripleInvocationFrames.consecutive_bank p d hh).2
  | inr a =>
    have he : a.1 ≤ p.castSucc ↔ a.1 < p.succ := by
      simp only [Fin.le_iff_val_le_val, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega
    simp [outgoing, incoming, he]
lemma consecutive_exponents (hh : 7 ≤ h) (p : Fin 2) (r : Role h) :
    (outgoing hh p.castSucc r).exponent = (incoming hh p.succ r).exponent :=
  Label.exponent_eq _ _ (consecutive_spaces hh p r)
def frames (L : Role h → Label (h ^ 3)) (X : Arrays h) : Arrays h :=
  fun r => frameMap (L r).exponent (X r)
def inverseFrames (L : Role h → Label (h ^ 3)) (X : Arrays h) : Arrays h :=
  fun r => frameMap (fun x => -(L r).exponent x) (X r)
lemma inverse_frames (L : Role h → Label (h ^ 3)) (X : Arrays h) : inverseFrames L (frames L X) = X := by
  funext r
  exact congrArg (fun T : Operator (ι := Fin (h ^ 3)) => T (X r)) (frameMap_inverse (L r).exponent).2
lemma cancel_of_exponents (L K : Role h → Label (h ^ 3))
    (he : ∀ r, (L r).exponent = (K r).exponent) (X : Arrays h) :
    inverseFrames K (frames L X) = X := by
  funext r
  change frameMap (fun x => -(K r).exponent x) (frameMap (L r).exponent (X r)) = X r
  rw [he r]
  exact congrArg (fun T : Operator (ι := Fin (h ^ 3)) => T (X r)) (frameMap_inverse (K r).exponent).2
lemma consecutive_cancel (hh : 7 ≤ h) (p : Fin 2) (X : Arrays h) :
    inverseFrames (incoming hh p.succ) (frames (outgoing hh p.castSucc) X) = X :=
  cancel_of_exponents _ _ (consecutive_exponents hh p) X
/-- Actual physical shears: the middle axis reverses rows and exchanges logical banks. -/
def scalarStage (p : Fin 3) (X : Arrays h) : Arrays h
  | .inl (b, d) =>
    if p = 1 then
      if b = 0 then X (.inl (0, d)) - X (.inl (1, d)) else X (.inl (1, d))
    else if b = 0 then X (.inl (0, d)) else X (.inl (1, d)) + X (.inl (0, d))
  | .inr a => X (.inr a)
def exchanged (X : Arrays h) : Arrays h
  | .inl (b, d) => if b = 0 then -X (.inl (1, d)) else X (.inl (0, d))
  | .inr a => X (.inr a)
lemma scalar_stages (X : Arrays h) : scalarStage 2 (scalarStage 1 (scalarStage 0 X)) = exchanged X := by
  funext r x
  cases r with
  | inl rd => rcases rd with ⟨b, d⟩; fin_cases b <;> simp [scalarStage, exchanged]
  | inr a => rfl
def framedStage (hh : 7 ≤ h) (p : Fin 3) (X : Arrays h) : Arrays h :=
  frames (outgoing hh p) (scalarStage p (inverseFrames (incoming hh p) X))
/-- Concrete boundaries telescope around the actual three physical scalar stages. -/
theorem framed_stages (hh : 7 ≤ h) (X : Arrays h) :
    framedStage hh 2 (framedStage hh 1 (framedStage hh 0 X)) =
      frames (outgoing hh 2) (exchanged (inverseFrames (incoming hh 0) X)) := by
  unfold framedStage
  have h0 (Y : Arrays h) : inverseFrames (incoming hh 1) (frames (outgoing hh 0) Y) = Y :=
    consecutive_cancel hh 0 Y
  have h1 (Y : Arrays h) : inverseFrames (incoming hh 2) (frames (outgoing hh 1) Y) = Y :=
    consecutive_cancel hh 1 Y
  rw [h1, h0, scalar_stages]
lemma initial_exponents (hh : 7 ≤ h) (d : Bank (Fin h)) :
    (incoming hh 0 (.inl (0, d))).exponent = lineExponent (TripleInvocationFrames.bankDirection d) ∧
    (incoming hh 0 (.inl (1, d))).exponent = (fun _ => 0) := by
  constructor
  · exact label_exponent_line _ _ (TripleInvocationFrames.bankDirection_norm d)
      (TripleInvocationFrames.source_bank d hh).1
  · exact label_exponent_bot _ (TripleInvocationFrames.source_bank d hh).2

lemma final_exponents (hh : 7 ≤ h) (d : Bank (Fin h)) :
    (outgoing hh 2 (.inl (0, d))).exponent = weightModFour ∧
    (outgoing hh 2 (.inl (1, d))).exponent = perpExponent (TripleInvocationFrames.bankDirection d) := by
  constructor
  · exact label_exponent_top _ (TripleInvocationFrames.sink_bank d hh).1
  · exact label_exponent_perp _ _ (TripleInvocationFrames.bankDirection_norm d)
      (TripleInvocationFrames.sink_bank d hh).2

lemma initial_auxiliary_exponent (hh : 7 ≤ h) (a : Aux h) :
    (incoming hh 0 (.inr a)).exponent = (fun _ => 0) := by
  have hn : ¬ a.1 < 0 := by simp
  exact label_exponent_bot _ (by simp [incoming, hn, zeroLabel])

lemma final_auxiliary_exponent (hh : 7 ≤ h) (a : Aux h) :
    (outgoing hh 2 (.inr a)).exponent = weightModFour := by
  have hn : a.1 ≤ 2 := by omega
  exact label_exponent_top _ (by simp [outgoing, hn, fullLabel])

abbrev State (h : ℕ) := NetworkTerminal.State (Bank (Fin h)) (Aux h) (Fin (h ^ 3))
def stateArrays (s : State h) : Arrays h
  | .inl (b, d) => if b = 0 then s.x d else s.y d
  | .inr a => s.auxiliary a

lemma source_inverse_arrays (hh : 7 ≤ h) (s : State h) :
    inverseFrames (incoming hh 0) (stateArrays s) =
      stateArrays (NetworkTerminal.sourceInverse TripleInvocationFrames.bankDirection s) := by
  funext r
  cases r with
  | inl rd =>
    rcases rd with ⟨b, d⟩
    fin_cases b
    · simp [inverseFrames, stateArrays, (initial_exponents hh d).1,
        NetworkTerminal.sourceInverse]
    · simp [inverseFrames, stateArrays, (initial_exponents hh d).2,
        NetworkTerminal.sourceInverse, neg_zero, frameMap_zero, LinearMap.id_apply]
  | inr a =>
    simp [inverseFrames, stateArrays, initial_auxiliary_exponent hh a,
      NetworkTerminal.sourceInverse, neg_zero, frameMap_zero, LinearMap.id_apply]

lemma exchanged_arrays (s : State h) : exchanged (stateArrays s) = stateArrays (NetworkTerminal.exchange s) := by
  funext r
  cases r with
  | inl rd => rcases rd with ⟨b, d⟩; fin_cases b <;> rfl
  | inr a => rfl

lemma sink_frames_arrays (hh : 7 ≤ h) (s : State h) :
    frames (outgoing hh 2) (stateArrays s) =
      stateArrays (NetworkTerminal.sinkFrames TripleInvocationFrames.bankDirection s) := by
  funext r
  cases r with
  | inl rd =>
    rcases rd with ⟨b, d⟩
    fin_cases b
    · simp [frames, stateArrays, (final_exponents hh d).1,
        NetworkTerminal.sinkFrames]
    · simp [frames, stateArrays, (final_exponents hh d).2,
        NetworkTerminal.sinkFrames]
  | inr a =>
    simp [frames, stateArrays, final_auxiliary_exponent hh a, NetworkTerminal.sinkFrames]

/-- No action premise: concrete three-stage semantics has the required dirty-data endpoint. -/
theorem framed_stages_endpoint (hh : 7 ≤ h) (s : State h) :
    framedStage hh 2 (framedStage hh 1 (framedStage hh 0 (stateArrays s))) =
      stateArrays (NetworkTerminal.sinkFrames TripleInvocationFrames.bankDirection
        (NetworkTerminal.exchange (NetworkTerminal.sourceInverse TripleInvocationFrames.bankDirection s))) := by
  rw [framed_stages, source_inverse_arrays, exchanged_arrays, sink_frames_arrays]

/-- Terminal correction restores the ordinary transform on all role arrays. -/
theorem corrected_stages_endpoint (_hh : 7 ≤ h) (s : State h) :
    NetworkTerminal.correction TripleInvocationFrames.bankDirection
      (NetworkTerminal.sinkFrames TripleInvocationFrames.bankDirection
        (NetworkTerminal.exchange (NetworkTerminal.sourceInverse TripleInvocationFrames.bankDirection s))) =
      NetworkTerminal.ordinary s :=
  NetworkTerminal.corrected_source_sink_exchange _ TripleInvocationFrames.bankDirection_norm s

end
end ExactFourierCircuits.TripleStageAction

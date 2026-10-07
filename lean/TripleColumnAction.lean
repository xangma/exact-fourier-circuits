import TripleStageAction
import ColumnSchedule
import ColumnTerminalFlat
set_option autoImplicit false
namespace ExactFourierCircuits.TripleColumnAction
open BinaryFrames BinaryTensor FrameSpectrum FramedScheduleWords
open TripleNetwork
open scoped BigOperators
noncomputable section
variable {h f : ℕ}
abbrev Role (h : ℕ) := TripleStageAction.Role h
abbrev Arrays (h f : ℕ) := Role h → Array (ι := Fin (f * h ^ 3))
def incoming (hh : 7 ≤ h) (f : ℕ) (p : Fin 3) : Role h → Label (f * h ^ 3) :=
  fun r => ColumnSchedule.columns f (TripleStageAction.incoming hh p r)
def outgoing (hh : 7 ≤ h) (f : ℕ) (p : Fin 3) : Role h → Label (f * h ^ 3) :=
  fun r => ColumnSchedule.columns f (TripleStageAction.outgoing hh p r)
lemma consecutive_spaces (hh : 7 ≤ h) (f : ℕ) (p : Fin 2) (r : Role h) :
    (outgoing hh f p.castSucc r).space = (incoming hh f p.succ r).space := by
  change ColumnSchedule.columnSpace f (TripleStageAction.outgoing hh p.castSucc r).space =
    ColumnSchedule.columnSpace f (TripleStageAction.incoming hh p.succ r).space
  rw [TripleStageAction.consecutive_spaces hh p r]
lemma consecutive_exponents (hh : 7 ≤ h) (f : ℕ) (p : Fin 2) (r : Role h) :
    (outgoing hh f p.castSucc r).exponent = (incoming hh f p.succ r).exponent :=
  Label.exponent_eq _ _ (consecutive_spaces hh f p r)
def frames (L : Role h → Label (f * h ^ 3)) (X : Arrays h f) : Arrays h f :=
  fun r => frameMap (L r).exponent (X r)
def inverseFrames (L : Role h → Label (f * h ^ 3)) (X : Arrays h f) : Arrays h f :=
  fun r => frameMap (fun x => -(L r).exponent x) (X r)
lemma cancel_of_exponents (L K : Role h → Label (f * h ^ 3))
    (he : ∀ r, (L r).exponent = (K r).exponent) (X : Arrays h f) :
    inverseFrames K (frames L X) = X := by
  funext r
  change frameMap (fun x => -(K r).exponent x) (frameMap (L r).exponent (X r)) = X r
  rw [he r]
  exact congrArg (fun T : Operator (ι := Fin (f * h ^ 3)) => T (X r)) (frameMap_inverse (K r).exponent).2
lemma consecutive_cancel (hh : 7 ≤ h) (f : ℕ) (p : Fin 2) (X : Arrays h f) :
    inverseFrames (incoming hh f p.succ) (frames (outgoing hh f p.castSucc) X) = X :=
  cancel_of_exponents _ _ (consecutive_exponents hh f p) X
def scalarStage (p : Fin 3) (X : Arrays h f) : Arrays h f
  | .inl (b, d) =>
    if p = 1 then
      if b = 0 then X (.inl (0, d)) - X (.inl (1, d)) else X (.inl (1, d))
    else if b = 0 then X (.inl (0, d)) else X (.inl (1, d)) + X (.inl (0, d))
  | .inr a => X (.inr a)
def exchanged (X : Arrays h f) : Arrays h f
  | .inl (b, d) => if b = 0 then -X (.inl (1, d)) else X (.inl (0, d))
  | .inr a => X (.inr a)
lemma scalar_stages (X : Arrays h f) : scalarStage 2 (scalarStage 1 (scalarStage 0 X)) = exchanged X := by
  funext r x
  cases r with
  | inl rd => rcases rd with ⟨b, d⟩; fin_cases b <;> simp [scalarStage, exchanged]
  | inr a => rfl
def framedStage (hh : 7 ≤ h) (f : ℕ) (p : Fin 3) (X : Arrays h f) : Arrays h f :=
  frames (outgoing hh f p) (scalarStage p (inverseFrames (incoming hh f p) X))
theorem framed_stages (hh : 7 ≤ h) (f : ℕ) (X : Arrays h f) :
    framedStage hh f 2 (framedStage hh f 1 (framedStage hh f 0 X)) =
      frames (outgoing hh f 2) (exchanged (inverseFrames (incoming hh f 0) X)) := by
  unfold framedStage
  have h0 (Y : Arrays h f) : inverseFrames (incoming hh f 1) (frames (outgoing hh f 0) Y) = Y :=
    consecutive_cancel hh f 0 Y
  have h1 (Y : Arrays h f) : inverseFrames (incoming hh f 2) (frames (outgoing hh f 1) Y) = Y :=
    consecutive_cancel hh f 1 Y
  rw [h1, h0, scalar_stages]

/-- The line and complement phases sum over physical columns, even when f is even. -/
def lineExponent {m : ℕ} (f : ℕ) (u : Vec (Fin m)) (ξ : Vec (Fin (f * m))) : ZMod 4 :=
  ∑ c, FrameSpectrum.lineExponent u (ColumnSchedule.column f m ξ c)
def perpExponent {m : ℕ} (f : ℕ) (u : Vec (Fin m)) (ξ : Vec (Fin (f * m))) : ZMod 4 :=
  ∑ c, FrameSpectrum.perpExponent u (ColumnSchedule.column f m ξ c)
lemma initial_exponents (hh : 7 ≤ h) (f : ℕ) (d : Bank (Fin h)) :
    (incoming hh f 0 (.inl (0, d))).exponent = lineExponent f (TripleInvocationFrames.bankDirection d) ∧
    (incoming hh f 0 (.inl (1, d))).exponent = (fun _ => 0) := by
  constructor
  · funext ξ
    rw [incoming, ColumnSchedule.columns_exponent_flat]
    simp only [(TripleStageAction.initial_exponents hh d).1, lineExponent]
  · funext ξ
    rw [incoming, ColumnSchedule.columns_exponent_flat]
    simp only [(TripleStageAction.initial_exponents hh d).2, Finset.sum_const_zero]
lemma columns_top_exponent {m : ℕ} (f : ℕ) (L : Label m) (hL : L.space = ⊤) :
    (ColumnSchedule.columns f L).exponent = weightModFour :=
  TripleStageAction.label_exponent_top _
    (by change ColumnSchedule.columnSpace f L.space = ⊤
        rw [hL]
        simp [ColumnSchedule.columnSpace, BinaryResiduals.tensorSpace_top_top])
lemma final_exponents (hh : 7 ≤ h) (f : ℕ) (d : Bank (Fin h)) :
    (outgoing hh f 2 (.inl (0, d))).exponent = weightModFour ∧
    (outgoing hh f 2 (.inl (1, d))).exponent = perpExponent f (TripleInvocationFrames.bankDirection d) := by
  constructor
  · exact columns_top_exponent _ _ (TripleInvocationFrames.sink_bank d hh).1
  · funext ξ
    rw [outgoing, ColumnSchedule.columns_exponent_flat]
    simp only [(TripleStageAction.final_exponents hh d).2, perpExponent]
lemma initial_auxiliary_exponent (hh : 7 ≤ h) (f : ℕ) (a : TripleStageAction.Aux h) :
    (incoming hh f 0 (.inr a)).exponent = (fun _ => 0) := by
  funext ξ
  rw [incoming, ColumnSchedule.columns_exponent_flat]
  simp only [TripleStageAction.initial_auxiliary_exponent hh a, Finset.sum_const_zero]
lemma final_auxiliary_exponent (hh : 7 ≤ h) (f : ℕ) (a : TripleStageAction.Aux h) :
    (outgoing hh f 2 (.inr a)).exponent = weightModFour := by
  apply columns_top_exponent
  have hn : a.1 ≤ 2 := by omega
  simp [TripleStageAction.outgoing, hn, TripleStageAction.fullLabel]

abbrev State (h f : ℕ) := NetworkTerminal.State (Bank (Fin h)) (TripleStageAction.Aux h) (Fin (f * h ^ 3))
def stateArrays (s : State h f) : Arrays h f
  | .inl (b, d) => if b = 0 then s.x d else s.y d
  | .inr a => s.auxiliary a
def sourceInverse (f : ℕ) (s : State h f) : State h f :=
  ⟨fun d => frameMap (fun ξ => -lineExponent f (TripleInvocationFrames.bankDirection d) ξ) (s.x d), s.y, s.auxiliary⟩
def sinkFrames (f : ℕ) (s : State h f) : State h f :=
  ⟨fun d => frameMap weightModFour (s.x d),
   fun d => frameMap (perpExponent f (TripleInvocationFrames.bankDirection d)) (s.y d),
   fun a => frameMap weightModFour (s.auxiliary a)⟩
lemma source_inverse_arrays (hh : 7 ≤ h) (f : ℕ) (s : State h f) :
    inverseFrames (incoming hh f 0) (stateArrays s) = stateArrays (sourceInverse f s) := by
  funext r
  cases r with
  | inl rd =>
    rcases rd with ⟨b, d⟩
    fin_cases b
    · simp [inverseFrames, stateArrays, (initial_exponents hh f d).1, sourceInverse]
    · simp [inverseFrames, stateArrays, (initial_exponents hh f d).2, sourceInverse, frameMap_zero]
  | inr a => simp [inverseFrames, stateArrays, initial_auxiliary_exponent hh f a, sourceInverse, frameMap_zero]
lemma exchanged_arrays (s : State h f) : exchanged (stateArrays s) = stateArrays (NetworkTerminal.exchange s) := by
  funext r
  cases r with
  | inl rd => rcases rd with ⟨b, d⟩; fin_cases b <;> rfl
  | inr a => rfl
lemma sink_frames_arrays (hh : 7 ≤ h) (f : ℕ) (s : State h f) :
    frames (outgoing hh f 2) (stateArrays s) = stateArrays (sinkFrames f s) := by
  funext r
  cases r with
  | inl rd =>
    rcases rd with ⟨b, d⟩
    fin_cases b
    · simp [frames, stateArrays, (final_exponents hh f d).1, sinkFrames]
    · simp [frames, stateArrays, (final_exponents hh f d).2, sinkFrames]
  | inr a => simp [frames, stateArrays, final_auxiliary_exponent hh f a, sinkFrames]
/-- Concrete copied-stage semantics; no master-word action is assumed. -/
theorem framed_stages_endpoint (hh : 7 ≤ h) (f : ℕ) (s : State h f) :
    framedStage hh f 2 (framedStage hh f 1 (framedStage hh f 0 (stateArrays s))) =
      stateArrays (sinkFrames f (NetworkTerminal.exchange (sourceInverse f s))) := by
  rw [framed_stages, source_inverse_arrays, exchanged_arrays, sink_frames_arrays]
def globalDirection (f : ℕ) (d : Bank (Fin h)) : Vec (Fin (f * h ^ 3)) :=
  ColumnTerminalFlat.direction f (TripleInvocationFrames.bankDirection d)

def endpoint (f : ℕ) (s : State h f) : State h f :=
  sinkFrames f (NetworkTerminal.exchange (sourceInverse f s))

/-- Actual copied-source/sink cancellation, valid without an odd combined direction. -/
theorem corrected_stages_endpoint (_hh : 7 ≤ h) (f : ℕ) (s : State h f) :
    NetworkTerminal.correction (globalDirection f) (endpoint f s) = NetworkTerminal.ordinary s := by
  change ColumnTerminalFlat.correction f TripleInvocationFrames.bankDirection
    (ColumnTerminalFlat.sinkFrames f TripleInvocationFrames.bankDirection
      (NetworkTerminal.exchange (ColumnTerminalFlat.sourceInverse f TripleInvocationFrames.bankDirection s))) = _
  exact ColumnTerminalFlat.corrected_source_sink_exchange f _ TripleInvocationFrames.bankDirection_norm s

end
end ExactFourierCircuits.TripleColumnAction

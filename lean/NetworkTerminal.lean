import BinaryColumns
import BinaryResiduals
import TripleCounting

/- Exact source/sink frame cancellation and terminal physical correction.
   Constructing the intervening labeled gate schedule remains separate. -/
namespace ExactFourierCircuits.NetworkTerminal
open BinaryFrames BinaryTensor BinaryResiduals FrameSpectrum
noncomputable section
variable {ι δ β : Type*} [Fintype ι] [DecidableEq ι]

@[ext] structure State (δ β ι : Type*) where
  x : δ → Vec ι → ℂ
  y : δ → Vec ι → ℂ
  auxiliary : β → Vec ι → ℂ

def sourceInverse (u : δ → Vec ι) (s : State δ β ι) : State δ β ι :=
  ⟨fun d => frameMap (fun ξ => -lineExponent (u d) ξ) (s.x d), s.y, s.auxiliary⟩

def exchange (s : State δ β ι) : State δ β ι := ⟨-s.y, s.x, s.auxiliary⟩

def sinkFrames (u : δ → Vec ι) (s : State δ β ι) : State δ β ι :=
  ⟨fun d => frameMap weightModFour (s.x d),
   fun d => frameMap (perpExponent (u d)) (s.y d),
   fun e => frameMap weightModFour (s.auxiliary e)⟩

/-- Translate physical Y first, then perform (X,Y)←(Y,-X). -/
def correction (u : δ → Vec ι) (s : State δ β ι) : State δ β ι :=
  ⟨fun d => translateMap (u d) (s.y d), -s.x, s.auxiliary⟩

def ordinary (s : State δ β ι) : State δ β ι :=
  ⟨fun d => frameMap weightModFour (s.x d), fun d => frameMap weightModFour (s.y d),
   fun e => frameMap weightModFour (s.auxiliary e)⟩

omit [Fintype ι] [DecidableEq ι] in
theorem translateMap_square (z : Vec ι) (f : Vec ι → ℂ) :
    translateMap z (translateMap z f) = f := by
  ext x
  simp [translateMap, Projection.translate, add_assoc]

/-- Whole-array terminal identity, including every arbitrary dirty auxiliary. -/
theorem corrected_source_sink_exchange (u : δ → Vec ι)
    (hu : ∀ d, dot (u d) (u d) = 1) (s : State δ β ι) :
    correction u (sinkFrames u (exchange (sourceInverse u s))) = ordinary s := by
  apply State.ext
  · funext d
    have h := congrArg (fun T : Operator (ι := ι) => T (s.x d))
      (terminal_frame_ratio (u d) (hu d))
    change translateMap (u d) (frameMap (perpExponent (u d))
      (frameMap (fun ξ => -lineExponent (u d) ξ) (s.x d))) = frameMap weightModFour (s.x d)
    rw [show frameMap (perpExponent (u d))
        (frameMap (fun ξ => -lineExponent (u d) ξ) (s.x d)) =
        translateMap (u d) (frameMap weightModFour (s.x d)) from h]
    exact translateMap_square _ _
  · funext d
    change -(frameMap weightModFour (-s.y d)) = frameMap weightModFour (s.y d)
    rw [map_neg, neg_neg]
  · rfl

def bankDirection (h : ℕ) (d : TripleNetwork.Bank (Fin h)) : Vec (Fin 3 → Fin h) :=
  tripleTensor 3 h (fun j => (d j).val)

theorem bankDirection_norm (h : ℕ) (d : TripleNetwork.Bank (Fin h)) :
    dot (bankDirection h d) (bankDirection h d) = 1 :=
  tripleTensor_norm 3 h (fun j => (d j).val) (fun j => (d j).property)

theorem bankDirection_weight (h : ℕ) (d : TripleNetwork.Bank (Fin h)) :
    weight (bankDirection h d) = 27 := by
  rw [bankDirection, tripleTensor_weight]
  · norm_num
  · exact fun j => (d j).property

theorem triple_corrected_source_sink_exchange (h : ℕ)
    (s : State (TripleNetwork.Bank (Fin h)) β (Fin 3 → Fin h)) :
    correction (bankDirection h)
      (sinkFrames (bankDirection h) (exchange (sourceInverse (bankDirection h) s))) = ordinary s :=
  corrected_source_sink_exchange _ (bankDirection_norm h) s

def columnSourceInverse (f : ℕ) (u : δ → Vec ι) (s : State δ β (Fin f × ι)) :
    State δ β (Fin f × ι) :=
  ⟨fun d => frameMap (fun ξ => -BinaryColumns.columnLineExponent (u d) ξ) (s.x d),
   s.y, s.auxiliary⟩

def columnSinkFrames (f : ℕ) (u : δ → Vec ι) (s : State δ β (Fin f × ι)) :
    State δ β (Fin f × ι) :=
  ⟨fun d => frameMap weightModFour (s.x d),
   fun d => frameMap (BinaryColumns.columnPerpExponent (u d)) (s.y d),
   fun e => frameMap weightModFour (s.auxiliary e)⟩

theorem corrected_column_source_sink_exchange (f : ℕ) (u : δ → Vec ι)
    (hu : ∀ d, dot (u d) (u d) = 1) (s : State δ β (Fin f × ι)) :
    correction (fun d => BinaryColumns.globalDirection (u d))
      (columnSinkFrames f u (exchange (columnSourceInverse f u s))) = ordinary s := by
  apply State.ext
  · funext d
    have h := congrArg (fun T : Operator (ι := Fin f × ι) => T (s.x d))
      (BinaryColumns.column_terminal_frame_ratio (f := f) (u d) (hu d))
    change translateMap (BinaryColumns.globalDirection (u d))
      (frameMap (BinaryColumns.columnPerpExponent (u d))
        (frameMap (fun ξ => -BinaryColumns.columnLineExponent (u d) ξ) (s.x d))) =
      frameMap weightModFour (s.x d)
    rw [show frameMap (BinaryColumns.columnPerpExponent (u d))
        (frameMap (fun ξ => -BinaryColumns.columnLineExponent (u d) ξ) (s.x d)) =
        translateMap (BinaryColumns.globalDirection (u d)) (frameMap weightModFour (s.x d)) from h]
    exact translateMap_square _ _
  · funext d
    change -(frameMap weightModFour (-s.y d)) = frameMap weightModFour (s.y d)
    rw [map_neg, neg_neg]
  · rfl

theorem triple_column_corrected_source_sink_exchange (f h : ℕ)
    (s : State (TripleNetwork.Bank (Fin h)) β (Fin f × (Fin 3 → Fin h))) :
    correction (fun d => BinaryColumns.globalDirection (bankDirection h d))
      (columnSinkFrames f (bankDirection h)
        (exchange (columnSourceInverse f (bankDirection h) s))) = ordinary s :=
  corrected_column_source_sink_exchange _ _ (bankDirection_norm h) s

end
end ExactFourierCircuits.NetworkTerminal

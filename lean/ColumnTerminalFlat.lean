import ColumnSchedule
import NetworkTerminal

set_option autoImplicit false

/- Terminal column identities in the literal flattened address coordinates.
   Only each original direction has norm one; its combined copy may have even norm. -/
namespace ExactFourierCircuits.ColumnTerminalFlat
open BinaryFrames BinaryTensor FrameSpectrum
open scoped BigOperators
noncomputable section

variable {m : ℕ} {δ β : Type*}

def lineExponent (f : ℕ) (u : Vec (Fin m)) (ξ : Vec (Fin (f * m))) : ZMod 4 :=
  ∑ c, FrameSpectrum.lineExponent u (ColumnSchedule.column f m ξ c)

def perpExponent (f : ℕ) (u : Vec (Fin m)) (ξ : Vec (Fin (f * m))) : ZMod 4 :=
  ∑ c, FrameSpectrum.perpExponent u (ColumnSchedule.column f m ξ c)

def direction (f : ℕ) (u : Vec (Fin m)) : Vec (Fin (f * m)) :=
  StageFrames.coordinates finProdFinEquiv (BinaryColumns.globalDirection (f := f) u)

lemma inverse_coordinates_column (f : ℕ) (ξ : Vec (Fin (f * m))) (c : Fin f) :
    BinaryColumns.column ((StageFrames.coordinates finProdFinEquiv).symm ξ) c =
      ColumnSchedule.column f m ξ c := rfl

lemma lineExponent_coordinates (f : ℕ) (u : Vec (Fin m)) (ξ : Vec (Fin (f * m))) :
    lineExponent f u ξ = BinaryColumns.columnLineExponent u
      ((StageFrames.coordinates finProdFinEquiv).symm ξ) := rfl

lemma perpExponent_coordinates (f : ℕ) (u : Vec (Fin m)) (ξ : Vec (Fin (f * m))) :
    perpExponent f u ξ = BinaryColumns.columnPerpExponent u
      ((StageFrames.coordinates finProdFinEquiv).symm ξ) := rfl

lemma direction_dot (f : ℕ) (u : Vec (Fin m)) (ξ : Vec (Fin (f * m))) :
    dot (direction f u) ξ = dot (BinaryColumns.globalDirection u)
      ((StageFrames.coordinates finProdFinEquiv).symm ξ) := by
  unfold direction
  have h := StageFrames.coordinates_dot finProdFinEquiv
    (BinaryColumns.globalDirection u) ((StageFrames.coordinates finProdFinEquiv).symm ξ)
  simpa only [LinearEquiv.apply_symm_apply] using h

lemma weightModFour_coordinates (f : ℕ) (ξ : Vec (Fin (f * m))) :
    weightModFour ((StageFrames.coordinates finProdFinEquiv).symm ξ) = weightModFour ξ := by
  have h := ColumnSchedule.coordinates_weightModFour finProdFinEquiv
    ((StageFrames.coordinates finProdFinEquiv).symm ξ)
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

theorem terminal_phase (f : ℕ) (u : Vec (Fin m)) (hu : dot u u = 1)
    (ξ : Vec (Fin (f * m))) :
    phase (perpExponent f u ξ - lineExponent f u ξ) =
      phase (weightModFour ξ) * binarySign (dot (direction f u) ξ) := by
  rw [lineExponent_coordinates, perpExponent_coordinates,
    BinaryColumns.column_terminal_phase u _ hu, weightModFour_coordinates, ← direction_dot]

/-- The whole-array terminal ratio is valid for every column count, including zero. -/
theorem terminal_frame_ratio (f : ℕ) (u : Vec (Fin m)) (hu : dot u u = 1) :
    (frameMap (perpExponent f u)).comp (frameMap (fun ξ => -lineExponent f u ξ)) =
      (translateMap (direction f u)).comp (frameMap weightModFour) := by
  apply operator_eq_of_characters
  intro ξ
  simp only [LinearMap.comp_apply, frameMap_character, map_smul,
    translate_character, smul_smul]
  congr 1
  calc
    _ = phase (perpExponent f u ξ - lineExponent f u ξ) := by
      rw [← phase_add, add_comm, sub_eq_add_neg]
    _ = _ := terminal_phase f u hu ξ

def sourceInverse (f : ℕ) (u : δ → Vec (Fin m))
    (s : NetworkTerminal.State δ β (Fin (f * m))) : NetworkTerminal.State δ β (Fin (f * m)) :=
  ⟨fun d => frameMap (fun ξ => -lineExponent f (u d) ξ) (s.x d), s.y, s.auxiliary⟩

def sinkFrames (f : ℕ) (u : δ → Vec (Fin m))
    (s : NetworkTerminal.State δ β (Fin (f * m))) : NetworkTerminal.State δ β (Fin (f * m)) :=
  ⟨fun d => frameMap weightModFour (s.x d),
   fun d => frameMap (perpExponent f (u d)) (s.y d),
   fun e => frameMap weightModFour (s.auxiliary e)⟩

def correction (f : ℕ) (u : δ → Vec (Fin m))
    (s : NetworkTerminal.State δ β (Fin (f * m))) : NetworkTerminal.State δ β (Fin (f * m)) :=
  NetworkTerminal.correction (fun d => direction f (u d)) s

/-- Source/sink cancellation on the actual flat address, for arbitrary dirty auxiliaries. -/
theorem corrected_source_sink_exchange (f : ℕ) (u : δ → Vec (Fin m))
    (hu : ∀ d, dot (u d) (u d) = 1) (s : NetworkTerminal.State δ β (Fin (f * m))) :
    correction f u (sinkFrames f u (NetworkTerminal.exchange (sourceInverse f u s))) =
      NetworkTerminal.ordinary s := by
  apply NetworkTerminal.State.ext
  · funext d
    have h := congrArg (fun T : Operator (ι := Fin (f * m)) => T (s.x d))
      (terminal_frame_ratio f (u d) (hu d))
    change translateMap (direction f (u d))
      (frameMap (perpExponent f (u d))
        (frameMap (fun ξ => -lineExponent f (u d) ξ) (s.x d))) =
      frameMap weightModFour (s.x d)
    rw [show frameMap (perpExponent f (u d))
        (frameMap (fun ξ => -lineExponent f (u d) ξ) (s.x d)) =
        translateMap (direction f (u d)) (frameMap weightModFour (s.x d)) from h]
    exact NetworkTerminal.translateMap_square _ _
  · funext d
    change -(frameMap weightModFour (-s.y d)) = frameMap weightModFour (s.y d)
    rw [map_neg, neg_neg]
  · rfl

/-- Consume an independently proved network endpoint without assuming a copied-direction norm. -/
theorem corrected_of_endpoint (f : ℕ) (u : δ → Vec (Fin m))
    (hu : ∀ d, dot (u d) (u d) = 1)
    (T : NetworkTerminal.State δ β (Fin (f * m)) → NetworkTerminal.State δ β (Fin (f * m)))
    (hT : ∀ s, T s = sinkFrames f u (NetworkTerminal.exchange (sourceInverse f u s)))
    (s : NetworkTerminal.State δ β (Fin (f * m))) :
    correction f u (T s) = NetworkTerminal.ordinary s := by
  rw [hT]
  exact corrected_source_sink_exchange f u hu s

end
end ExactFourierCircuits.ColumnTerminalFlat

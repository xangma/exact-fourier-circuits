import UniformCalendarRenderSnapshot
import UniformLayerScheduleRestriction

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierCalendarEpoch
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformCalendarRenderTick

theorem tick_transpose {n : ℕ} (L : List (Layer n)) (t : ℕ) (ht : t<L.length) :
    tick (transpose L) t = (tick L (L.length-1-t)).transpose := by
  rw [tick_of_lt _ _ (by simpa using ht),tick_of_lt _ _ (by omega)]
  simp only [transpose,List.get_eq_getElem,List.getElem_reverse,List.length_map,
    List.getElem_map,Layer.transpose_matrix]

/-- Actual chronological stages, including both diagonal boundaries of N. -/
theorem symmetric_sandwich {n : ℕ} (left right d : Fin n → ℂ)
    (hl : ∀i,left i≠0) (hr : ∀i,right i≠0) (hd : ∀i,d i≠0)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    symmetric (sandwich left right hl hr f hf) d hd =
      [Layer.step (UniformLocalFourierWord.diagonalStep left hl)] ++
      transpose (toeplitz n f hf) ++
      [Layer.step (UniformLocalFourierWord.diagonalStep right hr),
       Layer.step (UniformLocalFourierWord.diagonalStep d hd),
       Layer.step (UniformLocalFourierWord.diagonalStep right hr)] ++
      toeplitz n f hf ++ [Layer.step (UniformLocalFourierWord.diagonalStep left hl)] := by
  simp [symmetric,sandwich,transpose,Layer.transpose,
    UniformLocalFourierWord.diagonalStep,UniformLocalFourierWord.transposeStep,List.append_assoc]

theorem full_length {n : ℕ} (left right d : Fin n → ℂ)
    (hl : ∀i,left i≠0) (hr : ∀i,right i≠0) (hd : ∀i,d i≠0)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    (symmetric (sandwich left right hl hr f hf) d hd).length =
      2*(toeplitz n f hf).length+5 := by
  rw [symmetric_length]
  simp only [sandwich,List.length_append,List.length_singleton]
  omega

/-- A forward event occupies the second genuine Toeplitz epoch. -/
def forwardStart (length eventStart : ℕ) := length+4+eventStart
/-- Reflection reverses global chronology, including shorter-child idle padding. -/
def transposeStart (length eventStart duration : ℕ) := 1+length-eventStart-duration

theorem reflected_clock (length eventStart duration elapsed : ℕ)
    (extent : eventStart+duration≤length) (active : elapsed<duration) :
    length-(transposeStart length eventStart duration+elapsed) =
      eventStart+(duration-1-elapsed) := by
  unfold transposeStart
  omega

theorem transpose_epoch {n : ℕ} (left right d : Fin n → ℂ)
    (hl : ∀i,left i≠0) (hr : ∀i,right i≠0) (hd : ∀i,d i≠0)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0)
    (t : ℕ) (ht : t<(toeplitz n f hf).length) :
    tick (symmetric (sandwich left right hl hr f hf) d hd) (1+t) =
      (tick (toeplitz n f hf) ((toeplitz n f hf).length-1-t)).transpose := by
  rw [symmetric_sandwich]
  simp only [List.append_assoc]
  rw [tick_append]
  simp only [List.length_singleton,show ¬1+t<1 by omega,↓reduceIte,Nat.add_sub_cancel_left]
  rw [tick_append,ite_eq_left (by simpa using ht),tick_transpose _ t ht]

theorem forward_epoch {n : ℕ} (left right d : Fin n → ℂ)
    (hl : ∀i,left i≠0) (hr : ∀i,right i≠0) (hd : ∀i,d i≠0)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0)
    (t : ℕ) (ht : t<(toeplitz n f hf).length) :
    tick (symmetric (sandwich left right hl hr f hf) d hd)
      ((toeplitz n f hf).length+4+t) = tick (toeplitz n f hf) t := by
  rw [symmetric_sandwich]
  simp only [List.append_assoc]
  rw [tick_append]
  simp only [List.length_singleton,show ¬(toeplitz n f hf).length+4+t<1 by omega,↓reduceIte]
  rw [tick_append,ite_eq_right (by simp only [transpose_length];omega)]
  rw [tick_append,ite_eq_right (by simp;omega)]
  have idx : (toeplitz n f hf).length+4+t-1-(transpose (toeplitz n f hf)).length-3=t := by
    simp only [transpose_length];omega
  rw [show [Layer.step (UniformLocalFourierWord.diagonalStep right hr),
       Layer.step (UniformLocalFourierWord.diagonalStep d hd),
       Layer.step (UniformLocalFourierWord.diagonalStep right hr)].length=3 from rfl,idx]
  rw [tick_append,ite_eq_left ht]

end
end ExactFourierCircuits.UniformFourierCalendarEpoch

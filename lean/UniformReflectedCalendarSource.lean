import UniformReflectedPhysicalCalendar

set_option autoImplicit false
namespace ExactFourierCircuits.UniformReflectedCalendarSource
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformLayerSnapshot
open UniformFourierCalendarSnapshot (join)
open UniformReflectedFourierCalendar

/-- The actual forward selector's reflected clock; its elapsed is used unchanged. -/
theorem upper_source {n : ℕ} (left right d : Fin n→ℂ)
    (hl : ∀i,left i≠0) (hr : ∀i,right i≠0) (hd : ∀i,d i≠0)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0)
    (g : ℕ) (positive:0<g) (upper:g≤(toeplitz n f hf).length) :
    full left right d hl hr hd f hf g=
      UniformAllAxisCalendarTensor.axisSnapshot (UniformBalancedToeplitz.plan n) f hf
        ((toeplitz n f hf).length-g) := by
  simp only [full,join,transpose_length]
  rw [ite_eq_right (by omega),ite_eq_left (by omega)]
  unfold reflected
  change (if g-1<(toeplitz n f hf).length then
    UniformAllAxisCalendarTensor.axisSnapshot (UniformBalancedToeplitz.plan n) f hf
      ((toeplitz n f hf).length-1-(g-1)) else UniformFourierCalendarSnapshot.idle n)=_
  rw [ite_eq_left (by omega)]
  congr 1
  omega

theorem forward_source {n : ℕ} (left right d : Fin n→ℂ)
    (hl : ∀i,left i≠0) (hr : ∀i,right i≠0) (hd : ∀i,d i≠0)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0)
    (t : ℕ) (active:t<(toeplitz n f hf).length) :
    full left right d hl hr hd f hf ((toeplitz n f hf).length+4+t)=
      UniformAllAxisCalendarTensor.axisSnapshot (UniformBalancedToeplitz.plan n) f hf t := by
  simp only [full,join,transpose_length]
  rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),
    ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left (by omega)]
  congr 1
  omega

end
end ExactFourierCircuits.UniformReflectedCalendarSource

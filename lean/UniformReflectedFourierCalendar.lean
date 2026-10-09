import UniformCalendarReflection
import UniformFourierCalendarSnapshot

set_option autoImplicit false
namespace ExactFourierCircuits.UniformReflectedFourierCalendar
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformBalancedToeplitz UniformLayerSnapshot
open UniformCalendarRenderTick UniformFourierCalendarSnapshot
open NewtonFourier CoefficientTime

def reflected {n : ℕ} (P : Plan n) (f : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f≠0) (t : ℕ) : Snapshot (Fin n) :=
  if t<(UniformLocalFourierLayers.render P f hf).length then
    UniformAllAxisCalendarTensor.axisSnapshot P f hf ((UniformLocalFourierLayers.render P f hf).length-1-t)
  else idle n

theorem reflected_matrix {n : ℕ} (P : Plan n) (f : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f≠0) (t : ℕ) :
    (reflected P f hf t).matrix=tick (transpose (UniformLocalFourierLayers.render P f hf)) t := by
  by_cases ht:t<(UniformLocalFourierLayers.render P f hf).length
  · simp only [reflected,ite_eq_left ht]
    exact UniformCalendarReflection.reflected_forward_snapshot P f hf t ht
  · simp only [reflected,ite_eq_right ht,idle_matrix]
    exact (tick_of_le (transpose (UniformLocalFourierLayers.render P f hf)) t (by simpa using Nat.le_of_not_gt ht)).symm

/-- Both epochs use the same genuinely generated forward event family. -/
def full {n : ℕ} (left right d : Fin n→ℂ)
    (hl : ∀i,left i≠0) (hr : ∀i,right i≠0) (hd : ∀i,d i≠0)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) : ℕ→Snapshot (Fin n) :=
  join 1 (single left hl)
    (join (transpose (toeplitz n f hf)).length (reflected (plan n) f hf)
      (join 1 (single right hr)
        (join 1 (single d hd)
          (join 1 (single right hr)
            (join (toeplitz n f hf).length
              (UniformAllAxisCalendarTensor.axisSnapshot (plan n) f hf) (single left hl))))))

theorem full_matrix {n : ℕ} (left right d : Fin n→ℂ)
    (hl : ∀i,left i≠0) (hr : ∀i,right i≠0) (hd : ∀i,d i≠0)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) (t : ℕ) :
    (full left right d hl hr hd f hf t).matrix=
      tick (symmetric (sandwich left right hl hr f hf) d hd) t := by
  rw [UniformFourierCalendarEpoch.symmetric_sandwich]
  unfold full
  simp only [List.append_assoc]
  exact join_matrix [_] _ _ _ (single_matrix left hl)
    (fun t => join_matrix _ _ _ _ (reflected_matrix _ _ _)
      (fun t => join_matrix [_] _ _ _ (single_matrix right hr)
        (fun t => join_matrix [_] _ _ _ (single_matrix d hd)
          (fun t => join_matrix [_] _ _ _ (single_matrix right hr)
            (fun t => join_matrix _ _ _ _ (UniformAllAxisCalendarTensor.axisSnapshot_matrix _ _ _)
              (single_matrix left hl) t) t) t) t) t) t

def selected {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) : ℕ→Snapshot (Fin n) :=
  full (fun j=>NewtonFourier.H omega j.val) (fun j=>scale omega j.val)
    (fun j=>(UniformNewton.diagonalValue omega j.val)⁻¹)
    (UniformNewton.Hvalue_ne_zero hroot) (UniformNewton.scaleValue_ne_zero hn hroot)
    (fun j=>inv_ne_zero (UniformNewton.diagonalValue_ne_zero hn hroot j)) (invH omega) (by simp)

theorem selected_matrix {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) (t : ℕ) :
    (selected hn hroot t).matrix=tick (schedule hn hroot) t := full_matrix ..

def specified (n t : ℕ) : Snapshot (Fin n) :=
  if hn:0<n then selected hn (Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hn)) t else idle n

theorem specified_matrix (n t : ℕ) :
    (specified n t).matrix=tick (specifiedSchedule n) t := by
  by_cases hn:0<n
  · simp only [specified,specifiedSchedule,dite_eq_left hn,selected_matrix]
  · simp [specified,specifiedSchedule,hn]

end
end ExactFourierCircuits.UniformReflectedFourierCalendar

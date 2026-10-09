import UniformTransposeCalendarSnapshot
import UniformAlternateFourierSchedule

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierCalendarSnapshot
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformBalancedToeplitz UniformLayerSnapshot
open UniformCalendarRenderTick
open NewtonFourier CoefficientTime

def idle (n : ℕ) : Snapshot (Fin n) := Snapshot.ofDiagonal (fun _=>1) (fun _=>one_ne_zero)

@[simp] theorem idle_matrix (n : ℕ) : (idle n).matrix=1 := by
  simp [idle]

def single {n : ℕ} (d : Fin n→ℂ) (hd : ∀i,d i≠0) (t : ℕ) : Snapshot (Fin n) :=
  if t=0 then Snapshot.ofDiagonal d hd else idle n

theorem single_matrix {n : ℕ} (d : Fin n→ℂ) (hd : ∀i,d i≠0) (t : ℕ) :
    (single d hd t).matrix=tick [Layer.step (UniformLocalFourierWord.diagonalStep d hd)] t := by
  cases t with
  | zero => simp [single,UniformLocalFourierWord.diagonalStep,WordStep.matrix]
  | succ t => simp [single]

def join {n : ℕ} (length : ℕ) (A B : ℕ→Snapshot (Fin n)) (t : ℕ) : Snapshot (Fin n) :=
  if t<length then A t else B (t-length)

theorem join_matrix {n : ℕ} (L R : List (Layer n)) (A B : ℕ→Snapshot (Fin n))
    (ha : ∀t,(A t).matrix=tick L t) (hb : ∀t,(B t).matrix=tick R t) (t : ℕ) :
    (join L.length A B t).matrix=tick (L++R) t := by
  rw [tick_append]
  unfold join
  split_ifs with on
  · exact ha t
  · exact hb _

/-- Every stage is explicit: genuine upper active unions, all boundary
coordinate diagonals, genuine forward active unions, then identity padding. -/
def full {n : ℕ} (left right d : Fin n→ℂ)
    (hl : ∀i,left i≠0) (hr : ∀i,right i≠0) (hd : ∀i,d i≠0)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) : ℕ→Snapshot (Fin n) :=
  join 1 (single left hl)
    (join (UniformTransposeTreeRender.render (plan n) f hf).length
      (UniformTransposeCalendarSnapshot.axisSnapshot (plan n) f hf)
      (join 1 (single right hr)
        (join 1 (single d hd)
          (join 1 (single right hr)
            (join (toeplitz n f hf).length
              (UniformAllAxisCalendarTensor.axisSnapshot (plan n) f hf) (single left hl))))))

theorem full_matrix {n : ℕ} (left right d : Fin n→ℂ)
    (hl : ∀i,left i≠0) (hr : ∀i,right i≠0) (hd : ∀i,d i≠0)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) (t : ℕ) :
    (full left right d hl hr hd f hf t).matrix =
      tick (UniformAlternateFourierSchedule.assembly
        (UniformTransposeTreeRender.render (plan n) f hf) (toeplitz n f hf) left right d hl hr hd) t := by
  unfold full UniformAlternateFourierSchedule.assembly
  simp only [List.append_assoc]
  exact join_matrix [_] _ _ _ (single_matrix left hl)
    (fun t => join_matrix _ _ _ _ (UniformTransposeCalendarSnapshot.axisSnapshot_matrix _ _ _)
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
    (selected hn hroot t).matrix=tick (UniformAlternateFourierSchedule.schedule hn hroot) t :=
  full_matrix ..

def specified (n t : ℕ) : Snapshot (Fin n) :=
  if hn : 0<n then selected hn (Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hn)) t else idle n

theorem specified_matrix (n t : ℕ) :
    (specified n t).matrix=tick (UniformAlternateFourierSchedule.specified n) t := by
  by_cases hn : 0<n
  · simp only [specified,UniformAlternateFourierSchedule.specified,dite_eq_left hn,selected_matrix]
  · simp [specified,UniformAlternateFourierSchedule.specified,hn]

end
end ExactFourierCircuits.UniformFourierCalendarSnapshot

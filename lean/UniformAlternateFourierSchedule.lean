import UniformTransposeTreeRender

set_option autoImplicit false
namespace ExactFourierCircuits.UniformAlternateFourierSchedule
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformBalancedToeplitz UniformLayerRestriction
open NewtonFourier CoefficientTime

def assembly {n : ℕ} (U L : List (Layer n)) (left right d : Fin n → ℂ)
    (hl : ∀i,left i≠0) (hr : ∀i,right i≠0) (hd : ∀i,d i≠0) : List (Layer n) :=
  [Layer.step (UniformLocalFourierWord.diagonalStep left hl)] ++ U ++
  [Layer.step (UniformLocalFourierWord.diagonalStep right hr),
   Layer.step (UniformLocalFourierWord.diagonalStep d hd),
   Layer.step (UniformLocalFourierWord.diagonalStep right hr)] ++ L ++
  [Layer.step (UniformLocalFourierWord.diagonalStep left hl)]

def schedule {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) : List (Layer n) :=
  assembly (UniformTransposeTreeRender.render (plan n) (invH omega) (by simp))
    (toeplitz n (invH omega) (by simp))
    (fun j=>NewtonFourier.H omega j.val) (fun j=>scale omega j.val)
    (fun j=>(UniformNewton.diagonalValue omega j.val)⁻¹)
    (UniformNewton.Hvalue_ne_zero hroot) (UniformNewton.scaleValue_ne_zero hn hroot)
    (fun j=>inv_ne_zero (UniformNewton.diagonalValue_ne_zero hn hroot j))

theorem assembly_matrix {n : ℕ} (U L : List (Layer n)) (left right d : Fin n → ℂ)
    (hl : ∀i,left i≠0) (hr : ∀i,right i≠0) (hd : ∀i,d i≠0)
    (hU : matrix U=(matrix L).transpose) :
    matrix (assembly U L left right d hl hr hd) =
      matrix (symmetric ([Layer.step (UniformLocalFourierWord.diagonalStep right hr)] ++ L ++
        [Layer.step (UniformLocalFourierWord.diagonalStep left hl)]) d hd) := by
  simp only [assembly,symmetric,matrix_append,matrix_cons,matrix_nil,
    one_mul,Layer.step_matrix,UniformLocalFourierWord.diagonalStep_matrix,transpose_matrix,
    hU,Matrix.transpose_mul,Matrix.diagonal_transpose,Matrix.mul_assoc]

theorem schedule_matrix {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) :
    matrix (schedule hn hroot) = RadixTwo.dft n omega := by
  unfold schedule toeplitz
  rw [assembly_matrix _ _ _ _ _ _ _ _ (UniformTransposeTreeRender.render_matrix _ _ _)]
  exact UniformLocalFourierLayers.schedule_matrix hn hroot

theorem schedule_length {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) :
    (schedule hn hroot).length=(UniformLocalFourierLayers.schedule hn hroot).length := by
  simp only [schedule,assembly,List.length_append,List.length_cons,List.length_nil,
    UniformTransposeTreeRender.render_length,UniformLocalFourierLayers.schedule,symmetric_length,
    Nschedule,sandwich,toeplitz]
  omega

theorem schedule_restricted {n : ℕ} (hn : 0<n) {omega : ℂ} (hroot : IsPrimitiveRoot omega n) :
    ScheduleRestricted (schedule hn hroot) := by
  intro l hl
  simp only [schedule,assembly,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with (((rfl|h)|rfl|rfl|rfl)|h)|rfl
  · exact full_diagonalStep_restricted _ _
  · exact UniformTransposeTreeRender.render_restricted _ _ _ l h
  · exact full_diagonalStep_restricted _ _
  · exact full_diagonalStep_restricted _ _
  · exact full_diagonalStep_restricted _ _
  · exact render_restricted _ _ _ l h
  · exact full_diagonalStep_restricted _ _

def specified (n : ℕ) : List (Layer n) :=
  if hn : 0<n then schedule hn (Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hn)) else []

theorem specified_matrix (n : ℕ) : matrix (specified n)=fourierMatrix n := by
  by_cases hn : 0<n
  · simp only [specified,dite_eq_left hn,schedule_matrix]
    rfl
  · have hz : n=0 := by omega
    subst n
    ext i j
    exact Fin.elim0 i

theorem specified_length (n : ℕ) : (specified n).length=(specifiedSchedule n).length := by
  by_cases hn : 0<n
  · simp only [specified,specifiedSchedule,dite_eq_left hn,schedule_length]
  · simp [specified,specifiedSchedule,hn]

end
end ExactFourierCircuits.UniformAlternateFourierSchedule

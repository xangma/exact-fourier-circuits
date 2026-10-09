import UniformGlobalMatchingScaleBankBridge
import UniformLayerRestriction

set_option autoImplicit false

namespace ExactFourierCircuits.UniformGlobalCalendarPhases
noncomputable section
open OAI.ExactFourier UniformGlobalMatchingScaleMachine TypedKernelWords

/-- The phase ABI is the literal word's matrix, not only a dispatch tag. -/
def phaseMatrix (mu : ℂ) : Phase → Matrix (Fin 2) (Fin 2) ℂ
  | .diagonal lane => Matrix.diagonal (factor mu lane)
  | .kernel => C

lemma diagonal_eq (x y : ℂ) :
    ExactFourierCircuits.diagonal x y = Matrix.diagonal (fun i : Fin 2 => if i = 0 then x else y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ExactFourierCircuits.diagonal]

lemma front_eq (t : ℂ) : (5 : ℂ) / (4 * t) = (5 / 4) / t := by
  simp [div_eq_mul_inv,mul_inv_rev,mul_assoc,mul_comm]

lemma back_eq (t : ℂ) : (4 : ℂ) * t / 5 = (4 / 5) * t := by ring

/-- Exact correspondence of all28 literal shear phases with the nine produced
factor lanes and the six genuine ordered C calls. -/
theorem word_phase_matrices (mu : ℂ) :
    (UniformLocalShear.word mu).map WordStep.matrix = phases.map (phaseMatrix mu) := by
  simp [UniformLocalShear.word,shearWord,hadamardWord,phases,blockPhases,
    phaseMatrix,diagonal_eq,factor,front_eq,back_eq]

/-- A single physical phase has precisely the corresponding literal word matrix. -/
theorem word_phase_matrix (mu : ℂ) (i : Fin 28) :
    ((UniformLocalShear.word mu).get
      ⟨i.val,by rw [UniformLocalFourierLayers.localShear_length];exact i.isLt⟩).matrix =
    phaseMatrix mu (phases.get ⟨i.val,by rw [phases_length];exact i.isLt⟩) := by
  have eq := congrArg (fun L : List (Matrix (Fin 2) (Fin 2) ℂ) => L[i.val]?) (word_phase_matrices mu)
  simpa only [List.get_eq_getElem,List.getElem?_map,List.getElem?_eq_getElem
    (show i.val < (UniformLocalShear.word mu).length by rw [UniformLocalFourierLayers.localShear_length];exact i.isLt),
    List.getElem?_eq_getElem (show i.val < phases.length by rw [phases_length];exact i.isLt),
    Option.map_some,Option.some.injEq] using eq

end
end ExactFourierCircuits.UniformGlobalCalendarPhases

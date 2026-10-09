import UniformTensorPhaseFusion
import UniformGlobalMatchingScaleMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformMatchingPhaseFusion
open OAI.ExactFourier
open UniformGlobalMatchingScaleMachine
open UniformTensorPhaseFusion
noncomputable section

/-- This matrix reads the exact factors printed by the actual scale writer. -/
def localMatrix (mu : ℂ) : Phase→Mat2
 | .diagonal lane=>diagonal (factor mu lane 0) (factor mu lane 1)
 | .kernel=>C

theorem front_eq (t : ℂ) : ((5:ℂ)/4)/t=5/(4*t) := by rw [div_div]
theorem back_eq (t : ℂ) : ((4:ℂ)/5)*t=4*t/5 := by ring

theorem phases_word (mu : ℂ) : phases.map (localMatrix mu)=
    (UniformLocalShear.word mu).map WordStep.matrix := by
  simp [phases,blockPhases,localMatrix,factor,UniformLocalShear.word,
    TypedKernelWords.shearWord,TypedKernelWords.hadamardWord,
    TypedKernelWords.diagonalStep_matrix,TypedKernelWords.forwardCall_matrix,
    front_eq,back_eq]

theorem phases_upperShear (mu : ℂ) : chronological (phases.map (localMatrix mu))=upperShear mu := by
  rw [phases_word]
  exact shear_chronological mu

theorem simultaneous_pairs {ι : Type} [Fintype ι] [DecidableEq ι] (mu : ι→ℂ) :
    chronological (phases.map (fun phase=>PiTensor.matrix (fun i=>localMatrix (mu i) phase)))=
      PiTensor.matrix (fun i=>upperShear (mu i)) := by
  have h:=tensor_chronological_congr (D:=fun _ : ι=>Fin 2)
    (phases.map (fun phase i=>localMatrix (mu i) phase)) (fun i=>upperShear (mu i))
    (by intro i;simpa only [List.map_map,Function.comp_def] using phases_upperShear (mu i))
  simpa only [List.map_map,Function.comp_def] using h

end
end ExactFourierCircuits.UniformMatchingPhaseFusion

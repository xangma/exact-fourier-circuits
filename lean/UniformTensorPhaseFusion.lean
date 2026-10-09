import UniformLocalShear
import OAI.Computability.FourierCircuit.PiTensor

set_option autoImplicit false
namespace ExactFourierCircuits.UniformTensorPhaseFusion
open OAI.ExactFourier
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {D : ι→Type} [∀i,Fintype (D i)] [∀i,DecidableEq (D i)]

/-- Matrices are listed in physical execution order. -/
def chronological {E : Type} [Fintype E] [DecidableEq E]
    (phases : List (Matrix E E ℂ)) : Matrix E E ℂ := phases.reverse.prod

/-- Simultaneously execute each phase on every axis: phase-wise tensor fusion
equals the tensor of the complete local words, including singleton identities. -/
theorem tensor_chronological (phases : List (∀i,Matrix (D i) (D i) ℂ)) :
    chronological (phases.map PiTensor.matrix)=
      PiTensor.matrix (fun i=>chronological (phases.map (fun A=>A i))) := by
  induction phases with
  | nil=>
    change (1 : Matrix (∀i,D i) (∀i,D i) ℂ)=PiTensor.matrix (1 : ∀i,Matrix (D i) (D i) ℂ)
    exact PiTensor.one.symm
  | cons A phases ih=>
    simp only [List.map_cons,chronological,List.reverse_cons,List.prod_append,List.prod_singleton] at *
    rw [ih,←PiTensor.mul]
    rfl

theorem tensor_chronological_congr (phases : List (∀i,Matrix (D i) (D i) ℂ))
    (result : ∀i,Matrix (D i) (D i) ℂ)
    (h : ∀i,chronological (phases.map (fun A=>A i))=result i) :
    chronological (phases.map PiTensor.matrix)=PiTensor.matrix result := by
  rw [tensor_chronological]
  exact congrArg PiTensor.matrix (funext h)

theorem shear_chronological (mu : ℂ) :
    chronological ((UniformLocalShear.word mu).map WordStep.matrix)=
      upperShear mu := by
  exact UniformLocalShear.word_matrix mu

end
end ExactFourierCircuits.UniformTensorPhaseFusion

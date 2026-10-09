import DFTModelAffineOffsets
import UniformMachine

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelAffine
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine
noncomputable section

/-- Output selects the homogeneous channel; it contains no scalar injection. -/
def project : Prog false Tagged (c .left) := .comp (.atom .snd) (.atom .snd)

theorem project_run (z : Tagged.T) : run project z = ⟨z.2.2,3,0,True⟩ := by
  simp [project,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem matrix_zero {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    A.mulVec (fun _ => 0) = fun _ => 0 := by
  funext j
  simp [Matrix.mulVec,dotProduct]

/-- Linearity is used only at the terminal output. Affine intermediate
offsets may be nonzero. -/
theorem project_of_zero_input {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (x : Fin n → ℂ) (z : Fin m → Tagged.T)
    (total : ∀j, (z j).2.1 + (z j).2.2 = A.mulVec x j)
    (offset : ∀j, (z j).2.1 = A.mulVec (fun _ => 0) j) :
    ∀j, (run project (z j)).val = A.mulVec x j := by
  intro j
  have off : (z j).2.1 = 0 := by simpa only [matrix_zero] using offset j
  rw [project_run]
  simpa only [off,zero_add] using total j

def OutputRepresents {n : ℕ} (z : Fin n → Tagged.T) (s : State) : Prop :=
  ∀j, s.outputs j.val = some ((z j).2.1 + (z j).2.2)

def ZeroOffsets {n : ℕ} (z : Fin n → Tagged.T) (s : State) : Prop :=
  ∀j, s.outputs j.val = some (z j).2.1

/-- An actual zero-input source output equal to zero justifies dropping the
offset. The compiler still has to establish both output representation facts. -/
theorem source_output_projection {n : ℕ} (x : Fin n → ℂ) (z : Fin n → Tagged.T)
    (s zeroState : State) (dft : ComputesDFT n x s)
    (zero : ∀j : Fin n, zeroState.outputs j.val = some 0)
    (values : OutputRepresents z s) (offsets : ZeroOffsets z zeroState) :
    ∀j, (run project (z j)).val = (OAI.ExactFourier.fourierMatrix n).mulVec x j := by
  apply project_of_zero_input
  · intro j
    exact Option.some.inj ((values j).symm.trans (dft j))
  · intro j
    have off : (z j).2.1 = 0 := Option.some.inj ((offsets j).symm.trans (zero j))
    simpa only [matrix_zero] using off

end
end ExactFourierCircuits.DFTModelAffine

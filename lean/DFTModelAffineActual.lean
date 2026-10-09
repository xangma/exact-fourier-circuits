import DFTModelAffinePaired
import DFTModelAffineProjection
import DFTModelAdmissibilityActual

set_option autoImplicit false

/-! Terminal affine projection for the actual fixed DFT witness. This does
not assert that its memory/control translation has already been constructed. -/
namespace ExactFourierCircuits.DFTModelAffine
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAdmissibilityControl
noncomputable section
attribute [local irreducible] Nat.add Nat.mul UniformFinalOuterProgram.program
  UniformRecursiveSavingProgram.program UniformActualGlobalClockProgram.program

theorem paired_project_zero (a a0 : Scalar) (zero : a0.value = 0) :
    (run project (encodePaired a a0)).val = a.value := by
  rw [project_run]
  simp only [encodePaired,tagged,zero,sub_zero]

theorem paired_terminal_projection {n : ℕ} (x : Fin n → ℂ)
    (a a0 : Fin n → Scalar) (s zeroState : State)
    (dft : ComputesDFT n x s)
    (zero : ∀j : Fin n, zeroState.outputs j.val = some 0)
    (values : ∀j, s.outputs j.val = some (a j).value)
    (baseline : ∀j, zeroState.outputs j.val = some (a0 j).value) :
    ∀j, (run project (encodePaired (a j) (a0 j))).val =
      (OAI.ExactFourier.fourierMatrix n).mulVec x j := by
  intro j
  have zerov : (a0 j).value = 0 := Option.some.inj ((baseline j).symm.trans (zero j))
  rw [paired_project_zero _ _ zerov]
  exact Option.some.inj ((values j).symm.trans (dft j))

/-- Semantic paired output cells of two concrete source runs. The tag is
irrelevant after output; the only executed output operation is projection. -/
def pairedOutputs {n : ℕ} (s zeroState : State) (j : Fin n) : Tagged.T :=
  tagged true ((zeroState.outputs j.val).getD 0)
    ((s.outputs j.val).getD 0 - (zeroState.outputs j.val).getD 0)

theorem actual_zero_projected {n : ℕ} (hn : 0 < n) (x : Fin n → ℂ) :
    ∃ ticks s zeroState,
      BoundedExecution UniformFinalOuterProgram.program n x
        (UniformFinalDFTExecution.B n) initial ticks s ∧
      BoundedExecution UniformFinalOuterProgram.program n (fun _ => 0)
        (UniformFinalDFTExecution.B n) initial ticks zeroState ∧
      StateMatch s zeroState ∧
      (∀j, (run project (pairedOutputs s zeroState j)).val =
        (OAI.ExactFourier.fourierMatrix n).mulVec x j) := by
  obtain ⟨ticks,s,zeroState,actual,baseline,same,dft,zero,_roots,_cost⟩ :=
    DFTModelAdmissibilityActual.actual_zero_match hn x
  refine ⟨ticks,s,zeroState,actual,baseline,same,?_⟩
  intro j
  rw [project_run]
  simp only [pairedOutputs,tagged,dft j,zero j,Option.getD_some,sub_zero]

end
end ExactFourierCircuits.DFTModelAffine

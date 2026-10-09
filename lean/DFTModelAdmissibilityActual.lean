import DFTModelAdmissibilityControl
import UniformFinalDFTExecution

set_option autoImplicit false

/-! The actual fixed DFT witness has the same charged control path and word
bounds on zero input. This follows from instruction semantics. Only the final
zero-output observation uses the existing DFT correctness theorem; no assertion
about individual homogeneous additions is inferred from that observation. -/
namespace ExactFourierCircuits.DFTModelAdmissibilityActual
open UniformMachine DFTModelAdmissibilityControl
noncomputable section
attribute [local irreducible] Nat.add Nat.mul UniformFinalOuterProgram.program
  UniformRecursiveSavingProgram.program UniformActualGlobalClockProgram.program

/-- Two actual executions of the same literal twenty-stage program, with the
same instruction count, integer/address/control structure and prepared values.
The zero run is produced from the original successful execution. -/
theorem actual_zero_match {n : ℕ} (hn : 0 < n) (x : Fin n → ℂ) :
    ∃ ticks u uz,
      BoundedExecution UniformFinalOuterProgram.program n x
        (UniformFinalDFTExecution.B n) initial ticks u ∧
      BoundedExecution UniformFinalOuterProgram.program n (fun _ => 0)
        (UniformFinalDFTExecution.B n) initial ticks uz ∧
      StateMatch u uz ∧ ComputesDFT n x u ∧
      (∀ j : Fin n, uz.outputs j.val = some 0) ∧
      u.rootOrders = [UniformMasterRootMachine.order n] ∧
      (ticks : ℝ) ≤ UniformFinalLinearTableCost.finalBudget
        UniformActualGlobalConstants.constants UniformRecursiveSelfCallMachine.W n := by
  obtain ⟨ticks,u,run,dft,roots,cost⟩ := UniformFinalDFTExecution.execution hn x
  obtain ⟨uz,zeroRun,same⟩ := initial_execution_match (y := fun _ => 0) run
  obtain ⟨zt,z,reference,zeroDFT,_roots,_cost⟩ :=
    UniformFinalDFTExecution.execution hn (fun _ => 0)
  have unique := zeroRun.executes.deterministic reference.executes
  have finalEq : uz = z := unique.2
  have zeroOutput : ∀ j : Fin n, uz.outputs j.val = some 0 := by
    intro j
    rw [finalEq]
    simpa only [Matrix.mulVec,dotProduct,mul_zero,Finset.sum_const_zero] using zeroDFT j
  exact ⟨ticks,u,uz,run,zeroRun,same,dft,zeroOutput,roots,cost⟩

end
end ExactFourierCircuits.DFTModelAdmissibilityActual

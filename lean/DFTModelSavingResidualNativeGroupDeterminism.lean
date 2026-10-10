import DFTModelSavingResidualNativeGroupLoop

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualNativeGroup
open UniformMachine DFTModelAdmissibilityControl
noncomputable section

/-- Halting executions of the same deterministic machine agree in both
charged length and final state. This is used only for closed gather helpers,
not for arbitrary nonhalting segments ending at the same program counter. -/
theorem boundedExecution_unique {p : Program} {n B t t0 : ℕ} {x : Fin n → ℂ}
  {s u u0 : State} (a : BoundedExecution p n x B s t u)
  (z : BoundedExecution p n x B s t0 u0) : t=t0 ∧ u=u0 := by
  induction a generalizing t0 u0 with
  | halt _ stopped=>
    cases z with
    | halt _ stopped0=>
      exact ⟨rfl,StepResult.halted.inj (stopped.symm.trans stopped0)⟩
    | next _ step _=>rw [stopped] at step;cases step
  | next _ step tail ih=>
    cases z with
    | halt _ stopped=>rw [stopped] at step;cases step
    | next _ step0 tail0=>
      have same:=StepResult.running.inj (step.symm.trans step0)
      subst same
      obtain ⟨ticks,last⟩:=ih tail0
      exact ⟨congrArg (fun t=>t+1) ticks,last⟩

theorem paired_execution {p : Program} {n B t t0 : ℕ} {x : Fin n → ℂ}
  {s s0 u u0 : State} (a : BoundedExecution p n x B s t u)
  (z : BoundedExecution p n (fun _=>0) B s0 t0 u0) (same : StateMatch s s0) :
  t=t0 ∧ StateMatch u u0 := by
  obtain ⟨v,run,matched⟩:=boundedExecution_match (y:=fun _=>0) a same
  obtain ⟨ticks,last⟩:=boundedExecution_unique run z
  subst v
  exact ⟨ticks,matched⟩

end
end ExactFourierCircuits.DFTModelSavingResidualNativeGroup

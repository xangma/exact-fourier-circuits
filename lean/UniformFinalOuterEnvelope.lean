import UniformFinalOuterCostJoin

/-!
# Quantifiers and polynomial words for the final theorem

*An explicit power saving for the exact discrete Fourier transform*, OpenAI
math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, Theorem 1.1 and
(1.2), PDF p. 2 (`thm:main`, `eq:main-bound`); §5.4, PDF pp. 23–24.
This module is the logical adapter for the paper's final estimate and word
bound. It does not construct an execution: `of_execution` requires the
actual empty-start run subsequently supplied by `UniformFinalDFTExecution`.
-/

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalOuterEnvelope
open UniformMachine
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants

/-- Logical finish using the already proved shared polynomial word bound.
The caller constructs the real initial-state execution and its charged cost. -/
theorem of_execution
 (actual:∀n,0<n→∀x:Fin n→ℂ,∃t:ℕ,∃s:State,
  BoundedExecution UniformFinalOuterProgram.program n x (UniformJointAllocation.envelope c n) initial t s∧
  ComputesDFT n x s∧s.rootOrders=[UniformMasterRootMachine.order n]∧
  (t:ℝ)≤UniformFinalLinearTableCost.finalBudget c UniformRecursiveSelfCallMachine.W n):
 UniformDFTStatement UniformExponent.theta:=by
 /- §5.4, PDF p. 23: turn the proved O-bound into an absolute positive
 constant and eventual threshold. This step does not alter charged ticks. -/
 obtain ⟨K,positive,N,threshold,large⟩:=UniformFinalStatementBridge.eventual_runtime_bound
  UniformExponent.theta (UniformFinalLinearTableCost.finalBudget c UniformRecursiveSelfCallMachine.W)
  (UniformFinalLinearTableCost.finalBudget_isBigO_paper c UniformRecursiveSelfCallMachine.W)
 refine ⟨UniformFinalOuterProgram.program,K,positive,N,UniformJointAllocation.degree c,
  threshold,UniformJointAllocation.degree_pos c,?_⟩
 intro n hn
 /- §5.3, (5.8)–(5.9), PDF p. 23: the specified order is fixed from n
 before quantifying input data. §5.4, PDF p. 24: enlarge the same run's
 word envelope to one polynomial with degree independent of n. -/
 have order:=UniformMasterRootMachine.order_bounds hn
 refine ⟨UniformMasterRootMachine.order n,order.1,order.2,?_⟩
 intro x
 obtain ⟨t,s,run,dft,roots,time⟩:=actual n hn x
 exact ⟨t,s,UniformGlobalEnvelope.execution_mono run (UniformJointAllocation.polynomial c hn),
  dft,roots,fun h=>time.trans (large n h)⟩
end
end ExactFourierCircuits.UniformFinalOuterEnvelope

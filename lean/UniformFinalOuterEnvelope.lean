import UniformFinalOuterCostJoin

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
 obtain ⟨K,positive,N,threshold,large⟩:=UniformFinalStatementBridge.eventual_runtime_bound
  UniformExponent.theta (UniformFinalLinearTableCost.finalBudget c UniformRecursiveSelfCallMachine.W)
  (UniformFinalLinearTableCost.finalBudget_isBigO_paper c UniformRecursiveSelfCallMachine.W)
 refine ⟨UniformFinalOuterProgram.program,K,positive,N,UniformJointAllocation.degree c,
  threshold,UniformJointAllocation.degree_pos c,?_⟩
 intro n hn
 have order:=UniformMasterRootMachine.order_bounds hn
 refine ⟨UniformMasterRootMachine.order n,order.1,order.2,?_⟩
 intro x
 obtain ⟨t,s,run,dft,roots,time⟩:=actual n hn x
 exact ⟨t,s,UniformGlobalEnvelope.execution_mono run (UniformJointAllocation.polynomial c hn),
  dft,roots,fun h=>time.trans (large n h)⟩
end
end ExactFourierCircuits.UniformFinalOuterEnvelope

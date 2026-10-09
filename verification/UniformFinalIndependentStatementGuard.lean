import UniformFinalDFTExecution
import Lean
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalDFTStatementGuard
open UniformMachine
noncomputable section

theorem namedStatement : UniformDFTStatement UniformExponent.theta :=
 UniformFinalDFTExecution.uniformDFT

theorem literalStatement :
 ∃p:Program,∃K:ℝ,0<K∧∃N degree:ℕ,3≤N∧0<degree∧
 ∀n:ℕ,0<n→∃D:ℕ,0<D∧D<1024*n^3∧
 ∀x:Fin n→ℂ,∃t:ℕ,∃s:State,
 BoundedExecution p n x ((n+2)^degree) initial t s∧
 (∀j:Fin n,s.outputs j.val=some ((OAI.ExactFourier.fourierMatrix n).mulVec x j))∧
 s.rootOrders=[D]∧
 (N≤n→(t:ℝ)≤K*((n:ℝ)*(Real.log (n:ℝ))^UniformExponent.theta*
  (Real.log (Real.log (n:ℝ)))^(4-UniformExponent.theta))) :=
 UniformFinalDFTExecution.uniformDFT

theorem actualExecution : ∀{n:ℕ},0<n→∀x:Fin n→ℂ,∃ticks:ℕ,∃u:State,
 BoundedExecution UniformFinalOuterProgram.program n x
  (UniformJointAllocation.envelope UniformActualGlobalConstants.constants n) initial ticks u∧
 ComputesDFT n x u∧u.rootOrders=[UniformMasterRootMachine.order n]∧
 (ticks:ℝ)≤UniformFinalLinearTableCost.finalBudget UniformActualGlobalConstants.constants
  UniformRecursiveSelfCallMachine.W n := UniformFinalDFTExecution.execution

theorem strictExponent : 0<UniformExponent.theta∧UniformExponent.theta<1 :=
 ⟨UniformExponent.theta_pos,UniformExponent.theta_lt_one⟩
theorem paperGap : UniformExponent.theta<1-(2:ℝ)/10^13 :=
 UniformExponent.theta_explicit_gap

open Lean Elab Command in
run_cmd do
 let info ← getConstInfo ``ExactFourierCircuits.UniformFinalDFTExecution.uniformDFT
 match info with
 | .thmInfo _ => pure ()
 | _ => throwError "Final uniformDFT is not a theorem declaration"
 let expected := mkApp (mkConst ``ExactFourierCircuits.UniformMachine.UniformDFTStatement)
  (mkConst ``ExactFourierCircuits.UniformExponent.theta)
 unless info.type == expected do
  throwError m!"Final theorem type differs from the exact no-binder target: {info.type}"
 liftIO <| IO.FS.writeFile "../logs/uniform-final-dft-audit-agent-20261009/statement-guard.json"
  (Json.compress (Json.mkObj [("exact_unconditional_type",toJson true),
   ("extra_premises",toJson ([]:List String)),("literal_statement_checked",toJson true),
   ("actual_initial_execution_checked",toJson true),("strict_exponent_and_paper_gap_checked",toJson true),
   ("theorem",toJson "ExactFourierCircuits.UniformFinalDFTExecution.uniformDFT")]))
end
end ExactFourierCircuits.UniformFinalDFTStatementGuard

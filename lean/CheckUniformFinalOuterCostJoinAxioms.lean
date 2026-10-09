import UniformFinalOuterCostJoin
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalLinearTableCost.finalBudget.eq_1
#print axioms ExactFourierCircuits.UniformFinalOuterCostJoin.V
#print axioms ExactFourierCircuits.UniformFinalOuterCostJoin.W
#print axioms ExactFourierCircuits.UniformFinalOuterCostJoin.bound
#print axioms ExactFourierCircuits.UniformFinalOuterCostJoin.prefixCost
#print axioms ExactFourierCircuits.UniformFinalOuterCostJoin.prefixCost.eq_1
#print axioms ExactFourierCircuits.UniformFinalOuterCostJoin.suffixCost
#print axioms ExactFourierCircuits.UniformFinalOuterCostJoin.suffixCost.eq_1

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalOuterCostJoin.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

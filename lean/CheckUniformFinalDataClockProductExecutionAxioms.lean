import UniformFinalDataClockProductExecution
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.execution
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.execution._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.stages_beforePC
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.stages_bound

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalDataClockProductExecution.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

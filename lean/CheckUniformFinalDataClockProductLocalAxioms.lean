import UniformFinalDataClockProductLocal
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result.beforePC
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result.table_actual
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.execution_local

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalDataClockProductLocal.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

import UniformRecursiveActualLocalAllowance
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformRecursiveActualLocalAllowance.actual_local_allowance
#print axioms ExactFourierCircuits.UniformRecursiveActualLocalAllowance.localUnit
#print axioms ExactFourierCircuits.UniformRecursiveActualLocalAllowance.localUnit_lower
#print axioms ExactFourierCircuits.UniformRecursiveActualLocalAllowance.width_positive

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformRecursiveActualLocalAllowance.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

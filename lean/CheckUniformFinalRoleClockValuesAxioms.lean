import UniformFinalRoleClockValues
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalRoleClockValues.data_numeric
#print axioms ExactFourierCircuits.UniformFinalRoleClockValues.data_numeric._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalRoleClockValues.generic_one
#print axioms ExactFourierCircuits.UniformFinalRoleClockValues.generic_zero
#print axioms ExactFourierCircuits.UniformFinalRoleClockValues.kernel_numeric
#print axioms ExactFourierCircuits.UniformFinalRoleClockValues.prepared
#print axioms ExactFourierCircuits.UniformFinalRoleClockValues.source

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalRoleClockValues.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

import UniformFinalCallerFacts
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalCallerFacts.saved_of_runtime

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalCallerFacts.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

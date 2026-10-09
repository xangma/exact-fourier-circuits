import UniformFinalRoleTableEntries
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalRoleTableEntries.data
#print axioms ExactFourierCircuits.UniformFinalRoleTableEntries.kernel

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalRoleTableEntries.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

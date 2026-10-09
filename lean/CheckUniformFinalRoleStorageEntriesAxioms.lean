import UniformFinalRoleStorageEntries
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalRoleStorageEntries.data
#print axioms ExactFourierCircuits.UniformFinalRoleStorageEntries.data._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalRoleStorageEntries.kernel
#print axioms ExactFourierCircuits.UniformFinalRoleStorageEntries.kernel._proof_1_1

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalRoleStorageEntries.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

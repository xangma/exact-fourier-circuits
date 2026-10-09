import UniformFinalRoleStorageAlpha
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalRoleStorageAlpha.execution_with_storage
#print axioms ExactFourierCircuits.UniformFinalRoleStorageAlpha.execution_with_storage._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalRoleStorageAlpha.execution_with_storage._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalRoleStorageAlpha.execution_with_storage._proof_1_3
#print axioms ExactFourierCircuits.UniformFinalRoleStorageAlpha.execution_with_storage._proof_1_4
#print axioms ExactFourierCircuits.UniformFinalRoleStorageAlpha.execution_with_storage._proof_1_5
#print axioms ExactFourierCircuits.UniformFinalRoleStorageAlpha.execution_with_storage._proof_1_6

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalRoleStorageAlpha.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

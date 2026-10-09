import UniformFinalRoleStorageCaller
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalRoleStorageCaller.data
#print axioms ExactFourierCircuits.UniformFinalRoleStorageCaller.data._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalRoleStorageCaller.data._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalRoleStorageCaller.data._proof_1_3
#print axioms ExactFourierCircuits.UniformFinalRoleStorageCaller.data._proof_1_4
#print axioms ExactFourierCircuits.UniformFinalRoleStorageCaller.data._proof_1_5
#print axioms ExactFourierCircuits.UniformFinalRoleStorageCaller.kernel

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalRoleStorageCaller.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

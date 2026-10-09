import UniformFinalRoleRetention
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.cache_all
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.cache_heaps
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.cache_heaps._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.core
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.core._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.core._proof_1_10
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.core._proof_1_11
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.core._proof_1_12
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.core._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.core._proof_1_3
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.core._proof_1_4
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.core._proof_1_5
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.core._proof_1_6
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.core._proof_1_7
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.core._proof_1_8
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.core._proof_1_9
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.data
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.low
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.saved
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.saved._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.saved._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.spectrum

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalRoleRetention.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

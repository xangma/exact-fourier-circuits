import UniformFinalOuterStartup
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalOuterStartup.Result
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.Result.cache
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.Result.cacheEntryOutputs
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.Result.cacheEntryPC
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.Result.cacheEntryRoots
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.Result.casesOn
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.Result.core
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.Result.data
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.Result.headers
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.Result.mk
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.Result.mk._flat_ctor
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.Result.rec
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.Result.recOn
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.execution
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.execution._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.execution._proof_1_10
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.execution._proof_1_11
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.execution._proof_1_12
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.execution._proof_1_13
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.execution._proof_1_14
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.execution._proof_1_15
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.execution._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.execution._proof_1_3
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.execution._proof_1_4
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.execution._proof_1_5
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.execution._proof_1_6
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.execution._proof_1_7
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.execution._proof_1_8
#print axioms ExactFourierCircuits.UniformFinalOuterStartup.execution._proof_1_9

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalOuterStartup.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

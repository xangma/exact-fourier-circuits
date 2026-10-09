import UniformFinalStartupPrefix
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalStartupPrefix.execution
#print axioms ExactFourierCircuits.UniformFinalStartupPrefix.execution._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalStartupPrefix.execution._proof_1_10
#print axioms ExactFourierCircuits.UniformFinalStartupPrefix.execution._proof_1_11
#print axioms ExactFourierCircuits.UniformFinalStartupPrefix.execution._proof_1_12
#print axioms ExactFourierCircuits.UniformFinalStartupPrefix.execution._proof_1_13
#print axioms ExactFourierCircuits.UniformFinalStartupPrefix.execution._proof_1_14
#print axioms ExactFourierCircuits.UniformFinalStartupPrefix.execution._proof_1_15
#print axioms ExactFourierCircuits.UniformFinalStartupPrefix.execution._proof_1_16
#print axioms ExactFourierCircuits.UniformFinalStartupPrefix.execution._proof_1_17
#print axioms ExactFourierCircuits.UniformFinalStartupPrefix.execution._proof_1_18
#print axioms ExactFourierCircuits.UniformFinalStartupPrefix.execution._proof_1_19
#print axioms ExactFourierCircuits.UniformFinalStartupPrefix.execution._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalStartupPrefix.execution._proof_1_20
#print axioms ExactFourierCircuits.UniformFinalStartupPrefix.execution._proof_1_21
#print axioms ExactFourierCircuits.UniformFinalStartupPrefix.execution._proof_1_3
#print axioms ExactFourierCircuits.UniformFinalStartupPrefix.execution._proof_1_4
#print axioms ExactFourierCircuits.UniformFinalStartupPrefix.execution._proof_1_5
#print axioms ExactFourierCircuits.UniformFinalStartupPrefix.execution._proof_1_6
#print axioms ExactFourierCircuits.UniformFinalStartupPrefix.execution._proof_1_7
#print axioms ExactFourierCircuits.UniformFinalStartupPrefix.execution._proof_1_8
#print axioms ExactFourierCircuits.UniformFinalStartupPrefix.execution._proof_1_9

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalStartupPrefix.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

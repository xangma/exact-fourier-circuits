import UniformFinalDFTExecution
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalDFTExecution.B
#print axioms ExactFourierCircuits.UniformFinalDFTExecution.V
#print axioms ExactFourierCircuits.UniformFinalDFTExecution.W
#print axioms ExactFourierCircuits.UniformFinalDFTExecution.execution
#print axioms ExactFourierCircuits.UniformFinalDFTExecution.execution._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalDFTExecution.uniformDFT

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalDFTExecution.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

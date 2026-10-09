import UniformFinalOuterSuffix
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalOuterProgram.program.eq_1
#print axioms ExactFourierCircuits.UniformFinalOuterSuffix.code_fit
#print axioms ExactFourierCircuits.UniformFinalOuterSuffix.code_fit._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalOuterSuffix.contains
#print axioms ExactFourierCircuits.UniformFinalOuterSuffix.execution
#print axioms ExactFourierCircuits.UniformFinalOuterSuffix.execution._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalOuterSuffix.full_size
#print axioms ExactFourierCircuits.UniformFinalOuterSuffix.prelude
#print axioms ExactFourierCircuits.UniformFinalOuterSuffix.prelude.eq_1
#print axioms ExactFourierCircuits.UniformFinalOuterSuffix.prelude_size
#print axioms ExactFourierCircuits.UniformFinalOuterSuffix.shape
#print axioms ExactFourierCircuits.UniformFinalOuterSuffix.suffix

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalOuterSuffix.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

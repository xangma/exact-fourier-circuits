import UniformConcreteFinalOutputTail
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformConcreteFinalOutputTail.budget
#print axioms ExactFourierCircuits.UniformConcreteFinalOutputTail.execution
#print axioms ExactFourierCircuits.UniformConcreteFinalOutputTail.fits
#print axioms ExactFourierCircuits.UniformConcreteFinalOutputTail.fits._proof_1_1
#print axioms ExactFourierCircuits.UniformConcreteFinalOutputTail.fits._proof_1_2
#print axioms ExactFourierCircuits.UniformConcreteFinalOutputTail.of_three_transform_heaps
#print axioms ExactFourierCircuits.UniformConcreteFinalOutputTail.target
#print axioms ExactFourierCircuits.UniformConcreteFinalOutputTail.volume

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformConcreteFinalOutputTail.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

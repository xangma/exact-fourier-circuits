import UniformAxisCacheAdvanceMachine
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformAxisCacheAdvanceMachine.advance
#print axioms ExactFourierCircuits.UniformAxisCacheAdvanceMachine.advance.eq_1
#print axioms ExactFourierCircuits.UniformAxisCacheAdvanceMachine.advance_code
#print axioms ExactFourierCircuits.UniformAxisCacheAdvanceMachine.advance_frame
#print axioms ExactFourierCircuits.UniformAxisCacheAdvanceMachine.advance_length
#print axioms ExactFourierCircuits.UniformAxisCacheAdvanceMachine.advance_safe
#print axioms ExactFourierCircuits.UniformAxisCacheAdvanceMachine.advance_safe._proof_1_2
#print axioms ExactFourierCircuits.UniformAxisCacheAdvanceMachine.advance_values
#print axioms ExactFourierCircuits.UniformAxisCacheAdvanceMachine.execution
#print axioms ExactFourierCircuits.UniformAxisCacheAdvanceMachine.execution._proof_1_1
#print axioms ExactFourierCircuits.UniformAxisCacheAdvanceMachine.execution._proof_1_2
#print axioms ExactFourierCircuits.UniformAxisCacheAdvanceMachine.halt_at
#print axioms ExactFourierCircuits.UniformAxisCacheAdvanceMachine.nat_succ
#print axioms ExactFourierCircuits.UniformAxisCacheAdvanceMachine.nat_succ._proof_1_1
#print axioms ExactFourierCircuits.UniformAxisCacheAdvanceMachine.program
#print axioms ExactFourierCircuits.UniformAxisCacheAdvanceMachine.program_length
#print axioms ExactFourierCircuits.UniformAxisCacheAdvanceMachine.scalar_succ
#print axioms ExactFourierCircuits.UniformAxisCacheAdvanceMachine.scalar_succ._proof_1_1
#print axioms ExactFourierCircuits.UniformAxisCacheAdvanceMachine.select_code

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformAxisCacheAdvanceMachine.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

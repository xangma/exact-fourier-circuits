import UniformFinalClockCache
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalClockCache.from_prefix
#print axioms ExactFourierCircuits.UniformFinalClockCache.prefix_all
#print axioms ExactFourierCircuits.UniformFinalClockCache.prefix_heaps
#print axioms ExactFourierCircuits.UniformFinalClockCache.role_all_pc
#print axioms ExactFourierCircuits.UniformFinalClockCache.role_inputs
#print axioms ExactFourierCircuits.UniformFinalClockCache.role_inputs._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalClockCache.role_inputs_pc

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalClockCache.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

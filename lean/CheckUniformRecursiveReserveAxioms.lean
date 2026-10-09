import UniformRecursiveReserve
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformRecursiveReserve.literals_fit
#print axioms ExactFourierCircuits.UniformRecursiveReserve.payload
#print axioms ExactFourierCircuits.UniformRecursiveReserve.payload_fit
#print axioms ExactFourierCircuits.UniformRecursiveReserve.reserve
#print axioms ExactFourierCircuits.UniformRecursiveReserve.stack_fit
#print axioms ExactFourierCircuits.UniformRecursiveReserve.stack_room
#print axioms ExactFourierCircuits.UniformRecursiveReserve.stack_room._proof_1_1
#print axioms ExactFourierCircuits.UniformRecursiveReserve.threshold_fit
#print axioms ExactFourierCircuits.UniformRecursiveReserve.width_fit

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformRecursiveReserve.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

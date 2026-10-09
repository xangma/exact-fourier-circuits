import UniformFixedNetworkMarkerMachine
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFixedNetworkMarkerMachine.advance_at
#print axioms ExactFourierCircuits.UniformFixedNetworkMarkerMachine.boundary_execution
#print axioms ExactFourierCircuits.UniformFixedNetworkMarkerMachine.execution
#print axioms ExactFourierCircuits.UniformFixedNetworkMarkerMachine.execution._proof_1_1
#print axioms ExactFourierCircuits.UniformFixedNetworkMarkerMachine.execution._proof_1_2
#print axioms ExactFourierCircuits.UniformFixedNetworkMarkerMachine.execution._proof_1_3
#print axioms ExactFourierCircuits.UniformFixedNetworkMarkerMachine.execution._proof_1_4
#print axioms ExactFourierCircuits.UniformFixedNetworkMarkerMachine.halt_at
#print axioms ExactFourierCircuits.UniformFixedNetworkMarkerMachine.layout_execution
#print axioms ExactFourierCircuits.UniformFixedNetworkMarkerMachine.program
#print axioms ExactFourierCircuits.UniformFixedNetworkMarkerMachine.program.eq_1
#print axioms ExactFourierCircuits.UniformFixedNetworkMarkerMachine.program_length
#print axioms ExactFourierCircuits.UniformFixedNetworkMarkerMachine.reader_code

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFixedNetworkMarkerMachine.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

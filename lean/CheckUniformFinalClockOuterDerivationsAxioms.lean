import UniformFinalClockOuterDerivations
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.movement
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.movement._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.movement._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.movement._proof_1_3
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.movement._proof_1_4
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.movement._proof_1_5
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.role_of_storage
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.role_of_storage._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.role_of_storage._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.role_of_table
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Spectrum.role

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalClockOuterDerivations.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

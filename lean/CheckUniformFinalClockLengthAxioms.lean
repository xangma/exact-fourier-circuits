import UniformFinalClockLength
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalClockLength.code
#print axioms ExactFourierCircuits.UniformFinalClockLength.local_length
#print axioms ExactFourierCircuits.UniformFinalClockLength.local_length._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalClockLength.specified_length
#print axioms ExactFourierCircuits.UniformFinalClockLength.specified_length._proof_1_1
#print axioms ExactFourierCircuits.UniformSynchronizedLayers.localSchedules.eq_1

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalClockLength.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

import UniformFinalThirdClockOutput
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalThirdClockOutput.AP
#print axioms ExactFourierCircuits.UniformFinalThirdClockOutput.B
#print axioms ExactFourierCircuits.UniformFinalThirdClockOutput.BP
#print axioms ExactFourierCircuits.UniformFinalThirdClockOutput.K
#print axioms ExactFourierCircuits.UniformFinalThirdClockOutput.Q
#print axioms ExactFourierCircuits.UniformFinalThirdClockOutput.S
#print axioms ExactFourierCircuits.UniformFinalThirdClockOutput.V
#print axioms ExactFourierCircuits.UniformFinalThirdClockOutput.execution
#print axioms ExactFourierCircuits.UniformFinalThirdClockOutput.execution._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalThirdClockOutput.zero_heap
#print axioms ExactFourierCircuits.UniformFinalThirdClockOutput.zero_numeric

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalThirdClockOutput.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

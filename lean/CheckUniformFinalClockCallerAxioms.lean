import UniformFinalClockCaller
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalClockCaller.AP
#print axioms ExactFourierCircuits.UniformFinalClockCaller.H
#print axioms ExactFourierCircuits.UniformFinalClockCaller.Saved
#print axioms ExactFourierCircuits.UniformFinalClockCaller.data
#print axioms ExactFourierCircuits.UniformFinalClockCaller.data._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalClockCaller.data_from_saved
#print axioms ExactFourierCircuits.UniformFinalClockCaller.directory
#print axioms ExactFourierCircuits.UniformFinalClockCaller.from_input
#print axioms ExactFourierCircuits.UniformFinalClockCaller.from_saved
#print axioms ExactFourierCircuits.UniformFinalClockCaller.from_saved._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalClockCaller.from_saved._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalClockCaller.from_saved._proof_1_3
#print axioms ExactFourierCircuits.UniformFinalClockCaller.from_saved._proof_1_4
#print axioms ExactFourierCircuits.UniformFinalClockCaller.from_saved._proof_1_5
#print axioms ExactFourierCircuits.UniformFinalClockCaller.kernel
#print axioms ExactFourierCircuits.UniformFinalClockCaller.kernel._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalClockCaller.kernel_from_prefix

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalClockCaller.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

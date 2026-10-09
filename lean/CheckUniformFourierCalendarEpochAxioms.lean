import UniformFourierCalendarEpoch
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFourierCalendarEpoch.forwardStart
#print axioms ExactFourierCircuits.UniformFourierCalendarEpoch.forward_epoch
#print axioms ExactFourierCircuits.UniformFourierCalendarEpoch.forward_epoch._proof_1_1
#print axioms ExactFourierCircuits.UniformFourierCalendarEpoch.forward_epoch._proof_1_2
#print axioms ExactFourierCircuits.UniformFourierCalendarEpoch.forward_epoch._proof_1_3
#print axioms ExactFourierCircuits.UniformFourierCalendarEpoch.forward_epoch._proof_1_4
#print axioms ExactFourierCircuits.UniformFourierCalendarEpoch.full_length
#print axioms ExactFourierCircuits.UniformFourierCalendarEpoch.full_length._proof_1_1
#print axioms ExactFourierCircuits.UniformFourierCalendarEpoch.reflected_clock
#print axioms ExactFourierCircuits.UniformFourierCalendarEpoch.reflected_clock._proof_1_1
#print axioms ExactFourierCircuits.UniformFourierCalendarEpoch.symmetric_sandwich
#print axioms ExactFourierCircuits.UniformFourierCalendarEpoch.tick_transpose
#print axioms ExactFourierCircuits.UniformFourierCalendarEpoch.tick_transpose._proof_1_1
#print axioms ExactFourierCircuits.UniformFourierCalendarEpoch.transposeStart
#print axioms ExactFourierCircuits.UniformFourierCalendarEpoch.transpose_epoch
#print axioms ExactFourierCircuits.UniformFourierCalendarEpoch.transpose_epoch._proof_1_1
#print axioms ExactFourierCircuits.UniformLocalFourierWord.diagonalStep.eq_1
#print axioms ExactFourierCircuits.UniformLocalFourierWord.transposeStep.eq_1
#print axioms ExactFourierCircuits.UniformLocalFourierWord.transposeStep.eq_2

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFourierCalendarEpoch.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

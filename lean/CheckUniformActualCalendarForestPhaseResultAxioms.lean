import UniformActualCalendarForestPhaseResult
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformActualCalendarForestPhaseResult.coefficientBase
#print axioms ExactFourierCircuits.UniformActualCalendarForestPhaseResult.descriptor
#print axioms ExactFourierCircuits.UniformActualCalendarForestPhaseResult.offset
#print axioms ExactFourierCircuits.UniformActualCalendarForestPhaseResult.operationIndex
#print axioms ExactFourierCircuits.UniformActualCalendarForestPhaseResult.operationIndex._proof_1
#print axioms ExactFourierCircuits.UniformActualCalendarForestPhaseResult.operationIndex._proof_2
#print axioms ExactFourierCircuits.UniformActualCalendarForestPhaseResult.phase_result
#print axioms ExactFourierCircuits.UniformActualCalendarForestPhaseResult.phase_result._proof_1
#print axioms ExactFourierCircuits.UniformActualCalendarForestPhaseResult.phase_result._proof_2
#print axioms ExactFourierCircuits.UniformActualCalendarForestPhaseResult.phase_result._proof_3
#print axioms ExactFourierCircuits.UniformActualCalendarForestPhaseResult.phase_result._proof_4
#print axioms ExactFourierCircuits.UniformActualCalendarForestPhaseResult.phase_result._proof_5
#print axioms ExactFourierCircuits.UniformActualCalendarForestPhaseResult.phase_result._proof_6
#print axioms ExactFourierCircuits.UniformActualCalendarForestPhaseResult.width

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformActualCalendarForestPhaseResult.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

import UniformGlobalCalendarPhases
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformGlobalCalendarPhases.back_eq
#print axioms ExactFourierCircuits.UniformGlobalCalendarPhases.diagonal_eq
#print axioms ExactFourierCircuits.UniformGlobalCalendarPhases.front_eq
#print axioms ExactFourierCircuits.UniformGlobalCalendarPhases.phaseMatrix
#print axioms ExactFourierCircuits.UniformGlobalCalendarPhases.phaseMatrix.eq_1
#print axioms ExactFourierCircuits.UniformGlobalCalendarPhases.phaseMatrix.eq_2
#print axioms ExactFourierCircuits.UniformGlobalCalendarPhases.phaseMatrix.match_1
#print axioms ExactFourierCircuits.UniformGlobalCalendarPhases.word_phase_matrices
#print axioms ExactFourierCircuits.UniformGlobalCalendarPhases.word_phase_matrix
#print axioms ExactFourierCircuits.UniformGlobalMatchingScaleMachine.blockPhases.eq_1
#print axioms ExactFourierCircuits.UniformGlobalMatchingScaleMachine.phases.eq_1

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformGlobalCalendarPhases.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

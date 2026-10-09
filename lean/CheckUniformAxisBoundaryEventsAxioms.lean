import UniformAxisBoundaryEvents
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformAxisBoundaryEvents.action
#print axioms ExactFourierCircuits.UniformAxisBoundaryEvents.action._proof_1
#print axioms ExactFourierCircuits.UniformAxisBoundaryEvents.action._proof_2
#print axioms ExactFourierCircuits.UniformAxisBoundaryEvents.action._proof_3
#print axioms ExactFourierCircuits.UniformAxisBoundaryEvents.action._proof_4
#print axioms ExactFourierCircuits.UniformAxisBoundaryEvents.event
#print axioms ExactFourierCircuits.UniformAxisBoundaryEvents.event._proof_1
#print axioms ExactFourierCircuits.UniformAxisBoundaryEvents.event.eq_1
#print axioms ExactFourierCircuits.UniformAxisBoundaryEvents.event_cached
#print axioms ExactFourierCircuits.UniformAxisBoundaryEvents.event_cached._proof_1_4
#print axioms ExactFourierCircuits.UniformAxisBoundaryEvents.event_cached._proof_1_5
#print axioms ExactFourierCircuits.UniformAxisBoundaryEvents.event_cached._proof_1_6
#print axioms ExactFourierCircuits.UniformAxisBoundaryEvents.selections
#print axioms ExactFourierCircuits.UniformBoundaryDiagonalMachine.poolEntry.eq_1
#print axioms ExactFourierCircuits.UniformGlobalCalendarDispatch.phaseFactor.eq_1
#print axioms ExactFourierCircuits.UniformGlobalCalendarDispatch.phaseFactor.eq_2

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformAxisBoundaryEvents.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

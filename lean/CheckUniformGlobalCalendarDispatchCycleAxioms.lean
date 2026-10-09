import UniformGlobalCalendarDispatchCycle
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformGlobalCalendarDispatch.Source
#print axioms ExactFourierCircuits.UniformGlobalCalendarDispatch.Source.match_1
#print axioms ExactFourierCircuits.UniformGlobalCalendarDispatch.cycle_execution
#print axioms ExactFourierCircuits.UniformGlobalCalendarDispatch.cycle_execution._proof_1_1
#print axioms ExactFourierCircuits.UniformGlobalCalendarDispatch.cycle_execution._proof_1_2
#print axioms ExactFourierCircuits.UniformGlobalCalendarDispatch.cycle_execution._proof_1_6
#print axioms ExactFourierCircuits.UniformGlobalCalendarDispatch.cycle_execution._proof_1_7
#print axioms ExactFourierCircuits.UniformGlobalCalendarDispatch.phaseCalls
#print axioms ExactFourierCircuits.UniformGlobalCalendarDispatch.phaseCalls.eq_1
#print axioms ExactFourierCircuits.UniformGlobalCalendarDispatch.phaseCalls.eq_2
#print axioms ExactFourierCircuits.UniformGlobalCalendarDispatch.phaseCalls.match_1
#print axioms ExactFourierCircuits.UniformGlobalCalendarDispatch.phaseFactor
#print axioms ExactFourierCircuits.UniformGlobalCalendarDispatch.phaseFactor.match_1
#print axioms ExactFourierCircuits.UniformGlobalCalendarDispatch.rowAction

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformGlobalCalendarDispatchCycle.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

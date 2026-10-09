import UniformActualCalendarMatchingSource
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformActualCalendarMatchingSource.cached_event
#print axioms ExactFourierCircuits.UniformActualCalendarMatchingSource.cached_event._proof_1_1
#print axioms ExactFourierCircuits.UniformActualCalendarMatchingSource.cached_event._proof_1_5
#print axioms ExactFourierCircuits.UniformActualCalendarMatchingSource.endpoints
#print axioms ExactFourierCircuits.UniformActualCalendarMatchingSource.endpoints.eq_1
#print axioms ExactFourierCircuits.UniformActualCalendarMatchingSource.endpoints_at
#print axioms ExactFourierCircuits.UniformActualCalendarMatchingSource.event
#print axioms ExactFourierCircuits.UniformActualCalendarMatchingSource.factor
#print axioms ExactFourierCircuits.UniformActualCalendarMatchingSource.factor.eq_1
#print axioms ExactFourierCircuits.UniformActualCalendarMatchingSource.factor.eq_2
#print axioms ExactFourierCircuits.UniformActualCalendarMatchingSource.factor.match_1
#print axioms ExactFourierCircuits.UniformActualCalendarMatchingSource.ordered_rows
#print axioms ExactFourierCircuits.UniformActualCalendarMatchingSource.pool_grid

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformActualCalendarMatchingSource.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

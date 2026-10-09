import UniformCalendarActualAtoms
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformCalendarActualAtoms.direct_prefix
#print axioms ExactFourierCircuits.UniformCalendarActualAtoms.direct_prefix._simp_1_4
#print axioms ExactFourierCircuits.UniformCalendarActualAtoms.durations
#print axioms ExactFourierCircuits.UniformCalendarActualAtoms.durations.eq_1
#print axioms ExactFourierCircuits.UniformCalendarActualAtoms.durations.eq_2
#print axioms ExactFourierCircuits.UniformCalendarActualAtoms.durations.match_1
#print axioms ExactFourierCircuits.UniformCalendarActualAtoms.durations_sum
#print axioms ExactFourierCircuits.UniformCalendarActualAtoms.durations_values
#print axioms ExactFourierCircuits.UniformCalendarActualAtoms.kind
#print axioms ExactFourierCircuits.UniformCalendarActualAtoms.kind_duration
#print axioms ExactFourierCircuits.UniformCalendarActualAtoms.records
#print axioms ExactFourierCircuits.UniformCalendarActualAtoms.records_duration
#print axioms ExactFourierCircuits.UniformCalendarActualAtoms.records_get
#print axioms ExactFourierCircuits.UniformCalendarActualAtoms.records_length
#print axioms ExactFourierCircuits.UniformCalendarActualAtoms.rectangle_prefix

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformCalendarActualAtoms.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

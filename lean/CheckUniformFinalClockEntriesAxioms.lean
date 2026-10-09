import UniformFinalClockEntries
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalClockEntries.Entry
#print axioms ExactFourierCircuits.UniformFinalClockEntries.Entry.boot
#print axioms ExactFourierCircuits.UniformFinalClockEntries.Entry.cache
#print axioms ExactFourierCircuits.UniformFinalClockEntries.Entry.casesOn
#print axioms ExactFourierCircuits.UniformFinalClockEntries.Entry.input
#print axioms ExactFourierCircuits.UniformFinalClockEntries.Entry.inputs
#print axioms ExactFourierCircuits.UniformFinalClockEntries.Entry.mk
#print axioms ExactFourierCircuits.UniformFinalClockEntries.Entry.mk._flat_ctor
#print axioms ExactFourierCircuits.UniformFinalClockEntries.Entry.rec
#print axioms ExactFourierCircuits.UniformFinalClockEntries.Entry.recOn
#print axioms ExactFourierCircuits.UniformFinalClockEntries.data
#print axioms ExactFourierCircuits.UniformFinalClockEntries.kernel

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalClockEntries.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

import UniformActualCalendarScan
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Bundle.events_scan
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Bundle.scan
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Bundle.scan.eq_1
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Family.scan
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Family.scan_selected
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan._sizeOf_1
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan._sizeOf_inst
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.append
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.casesOn
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.ctorIdx
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.empty
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.flatten
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.flatten._f
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.flatten._sunfold
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.flatten._unsafe_rec
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.flatten.eq_1
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.flatten.eq_2
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.flatten.eq_def
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.flatten.match_1
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.make
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.mk
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.mk._flat_ctor
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.mk.inj
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.mk.injEq
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.mk.noConfusion
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.mk.sizeOf_spec
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.noConfusion
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.noConfusionType
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.rec
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.recOn
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.records
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.selected
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.selected_append
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.selected_append._proof_1_1
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.selected_append._proof_1_2
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.selected_append._proof_1_3
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.selected_append._proof_1_4
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.selected_append._proof_1_5
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.Scan.selected_flatten
#print axioms ExactFourierCircuits.UniformActualCalendarRegistry.events_parameters

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformActualCalendarScan.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

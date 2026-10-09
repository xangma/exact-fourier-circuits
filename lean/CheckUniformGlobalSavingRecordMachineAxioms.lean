import UniformGlobalSavingRecordMachine
import Lean
set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.boot
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.boot.eq_1
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.cells
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.cells._f
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.cells._sunfold
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.cells._unsafe_rec
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.cells.eq_1
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.cells.eq_2
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.cells.eq_3
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.cells.eq_def
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.cells.match_1
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.cells.match_3
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.cells_apply
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.cells_length
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.cells_length._proof_1_5
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.cells_peak
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.cells_readable
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.execution
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.execution._proof_1_2
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.execution._proof_1_3
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.execution._proof_1_5
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.execution._simp_1_4
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.fixedTemplate
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.halt_at
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.program
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.program.eq_1
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.program_length
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.resolve
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.resolve.eq_1
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.resolve_cons
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.resolve_fixed
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.resolve_length
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.resolve_template
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.resolve_templates
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.template
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.template.eq_1
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.templates
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.templates.eq_1
#print axioms ExactFourierCircuits.UniformGlobalSavingRecordMachine.whole_code

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformGlobalSavingRecordMachine.".isPrefixOf name.toString then
   let axioms ← collectAxioms name
   for ax in axioms do
    unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
     throwError m!"Nonstandard axiom {ax} in {name}"
   logInfo m!"{name} depends on axioms: {axioms.toList}"

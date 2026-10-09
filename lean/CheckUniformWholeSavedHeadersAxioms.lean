import UniformWholeSavedHeaders
import Lean
set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.body_saved
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.broadcast_saved
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.chunk_saved
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.emit_saved
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.execution_saved
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.inverse_saved
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.matching_saved
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.packing_saved
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.pair_saved
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.phase_saved
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.relocate_saved
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.saved_mem
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.sector_saved
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.traversal_saved
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.whole_keeps
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.whole_keeps._proof_1_7
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.whole_saved
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.writesSaved
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.writesSaved._sparseCasesOn_1
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.writesSaved._sparseCasesOn_1.else_eq
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.writesSaved.eq_1
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.writesSaved.eq_2
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.writesSaved.eq_3
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.writesSaved.eq_4
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.writesSaved.eq_5
#print axioms ExactFourierCircuits.UniformWholeSavedHeaders.writesSaved.match_1

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformWholeSavedHeaders.".isPrefixOf name.toString then
   let axioms ← collectAxioms name
   for ax in axioms do
    unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
     throwError m!"Nonstandard axiom {ax} in {name}"
   logInfo m!"{name} depends on axioms: {axioms.toList}"

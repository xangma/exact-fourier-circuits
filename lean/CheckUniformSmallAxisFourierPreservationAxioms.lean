import UniformSmallAxisFourierPreservation
import Lean
set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.batch_below
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.copy_below
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.execution
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.execution._proof_1_1
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.execution._proof_1_10
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.execution._proof_1_11
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.execution._proof_1_12
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.execution._proof_1_2
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.execution._proof_1_3
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.execution._proof_1_4
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.execution._proof_1_5
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.execution._proof_1_6
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.execution._proof_1_7
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.execution._proof_1_8
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.execution._proof_1_9
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.execution_nat
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.keeps_nat
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.keeps_nat._proof_1_7
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.program_below
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.relocate_below
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.writesBelow
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.writesBelow._sparseCasesOn_1
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.writesBelow._sparseCasesOn_1.else_eq
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.writesBelow.eq_1
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.writesBelow.eq_2
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.writesBelow.eq_3
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.writesBelow.eq_4
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.writesBelow.eq_5
#print axioms ExactFourierCircuits.UniformSmallAxisFourierPreservation.writesBelow.match_1

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformSmallAxisFourierPreservation.".isPrefixOf name.toString then
   let axioms ← collectAxioms name
   for ax in axioms do
    unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
     throwError m!"Nonstandard axiom {ax} in {name}"
   logInfo m!"{name} depends on axioms: {axioms.toList}"

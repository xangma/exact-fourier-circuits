import UniformMatchingPhaseFusion
import Lean
set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformMatchingPhaseFusion.back_eq
#print axioms ExactFourierCircuits.UniformMatchingPhaseFusion.front_eq
#print axioms ExactFourierCircuits.UniformMatchingPhaseFusion.localMatrix
#print axioms ExactFourierCircuits.UniformMatchingPhaseFusion.localMatrix._proof_1
#print axioms ExactFourierCircuits.UniformMatchingPhaseFusion.localMatrix.eq_1
#print axioms ExactFourierCircuits.UniformMatchingPhaseFusion.localMatrix.eq_2
#print axioms ExactFourierCircuits.UniformMatchingPhaseFusion.localMatrix.match_1
#print axioms ExactFourierCircuits.UniformMatchingPhaseFusion.phases_upperShear
#print axioms ExactFourierCircuits.UniformMatchingPhaseFusion.phases_word
#print axioms ExactFourierCircuits.UniformMatchingPhaseFusion.simultaneous_pairs

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformMatchingPhaseFusion.".isPrefixOf name.toString then
   let axioms ← collectAxioms name
   for ax in axioms do
    unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
     throwError m!"Nonstandard axiom {ax} in {name}"
   logInfo m!"{name} depends on axioms: {axioms.toList}"

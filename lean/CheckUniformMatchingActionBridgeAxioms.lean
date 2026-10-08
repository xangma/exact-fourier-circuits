import UniformMatchingActionBridge
import Lean
set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformMatchingActionBridge.actualPhi
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.actualPhi.congr_simp
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.actualPhi_pair
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.actualPhi_pair._proof_1
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.actualPhi_pair._proof_1_1
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.actualWord_eq
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.actualWord_eq._simp_1_5
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.actual_capacity
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.actual_matching_action
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.inverseWord_eq
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.inverseWord_eq._proof_1_2
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.inverseWord_eq._simp_1_5
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.inverse_matching_action
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.matchingAction_runShears
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.matchingAction_runShears._proof_1_4
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.natShear
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.natShear._proof_1
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.natShear.eq_1
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.natShear_act
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.natShears_run
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.originalValues
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.originalValues.eq_1
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.originalValues_restrict
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.pairShear
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.pairShear._proof_1
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.pairShear._proof_2
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.pairShear._proof_3
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.pairShear._proof_4
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.pairShear.congr_simp
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.pairShear.eq_1
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.pairUpdate_unpacked
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.physicalShears
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.physicalShears._f
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.physicalShears._proof_1
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.physicalShears._proof_2
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.physicalShears._proof_3
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.physicalShears._proof_4
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.physicalShears._sunfold
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.physicalShears._unsafe_rec
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.physicalShears.congr_simp
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.physicalShears.eq_1
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.physicalShears.eq_2
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.physicalShears.eq_def
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.physicalShears.match_1
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.physicalShears_length
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.physicalShears_ofFn
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.physicalShears_ofFn._proof_1
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.shear_ext
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.unpackValues
#print axioms ExactFourierCircuits.UniformMatchingActionBridge.unpackValues.eq_1

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformMatchingActionBridge.".isPrefixOf name.toString then
   let axioms ← collectAxioms name
   for ax in axioms do
    unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
     throwError m!"Nonstandard axiom {ax} in {name}"
   logInfo m!"{name} depends on axioms: {axioms.toList}"

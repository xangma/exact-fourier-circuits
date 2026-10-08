import UniformSeedConjugateRetention
import Lean
set_option autoImplicit false
set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformSeedConjugateRetention.copy_execution
#print axioms ExactFourierCircuits.UniformSeedConjugateRetention.copy_execution._proof_1_1
#print axioms ExactFourierCircuits.UniformSeedConjugateRetention.copy_execution._proof_1_2
#print axioms ExactFourierCircuits.UniformSeedConjugateRetention.copy_execution._proof_1_3
#print axioms ExactFourierCircuits.UniformSeedConjugateRetention.copy_execution._proof_1_4
#print axioms ExactFourierCircuits.UniformSeedConjugateRetention.copy_execution._proof_1_5
#print axioms ExactFourierCircuits.UniformSeedConjugateRetention.copy_execution._proof_1_6
#print axioms ExactFourierCircuits.UniformSeedConjugateRetention.driver_frame
#print axioms ExactFourierCircuits.UniformSeedConjugateRetention.emit_execution
#print axioms ExactFourierCircuits.UniformSeedConjugateRetention.emit_execution._proof_1_1
#print axioms ExactFourierCircuits.UniformSeedConjugateRetention.execution
#print axioms ExactFourierCircuits.UniformSeedConjugateRetention.execution._proof_1_1
#print axioms ExactFourierCircuits.UniformSeedConjugateRetention.execution._proof_1_2
#print axioms ExactFourierCircuits.UniformSeedConjugateRetention.execution._proof_1_3
#print axioms ExactFourierCircuits.UniformSeedConjugateRetention.execution._proof_1_4
#print axioms ExactFourierCircuits.UniformSeedConjugateRetention.execution._proof_1_5
#print axioms ExactFourierCircuits.UniformSeedConjugateRetention.execution._proof_1_6
#print axioms ExactFourierCircuits.UniformSeedConjugateRetention.execution._proof_1_7
#print axioms ExactFourierCircuits.UniformSeedConjugateRetention.keeps_driver
#print axioms ExactFourierCircuits.UniformSeedConjugateRetention.keeps_driver._proof_1_3
#print axioms ExactFourierCircuits.UniformSeedConjugateRetention.keeps_driver._proof_1_6
#print axioms ExactFourierCircuits.UniformSeedConjugateRetention.keeps_driver._proof_1_7

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformSeedConjugateRetention.".isPrefixOf name.toString then
   let axioms ← collectAxioms name
   logInfo m!"'{name}' depends on axioms: {axioms.toList}"
   for ax in axioms do
    unless ax == `propext || ax == `Quot.sound || ax == `Classical.choice do
     throwError m!"Forbidden axiom {ax} in {name}"

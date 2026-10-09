import TypedKernelWords
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.Hprime.eq_1
#print axioms ExactFourierCircuits.TypedKernelWords.C2
#print axioms ExactFourierCircuits.TypedKernelWords.Step
#print axioms ExactFourierCircuits.TypedKernelWords.compile_inverse
#print axioms ExactFourierCircuits.TypedKernelWords.compile_nonzero_shear
#print axioms ExactFourierCircuits.TypedKernelWords.diagonalStep
#print axioms ExactFourierCircuits.TypedKernelWords.diagonalStep.congr_simp
#print axioms ExactFourierCircuits.TypedKernelWords.diagonalStep.eq_1
#print axioms ExactFourierCircuits.TypedKernelWords.diagonalStep_matrix
#print axioms ExactFourierCircuits.TypedKernelWords.diagonal_isMonomial
#print axioms ExactFourierCircuits.TypedKernelWords.embeddedCall_refl
#print axioms ExactFourierCircuits.TypedKernelWords.embeddedCall_reindex
#print axioms ExactFourierCircuits.TypedKernelWords.forwardCall
#print axioms ExactFourierCircuits.TypedKernelWords.forwardCall.eq_1
#print axioms ExactFourierCircuits.TypedKernelWords.forwardCall_matrix
#print axioms ExactFourierCircuits.TypedKernelWords.hadamardWord
#print axioms ExactFourierCircuits.TypedKernelWords.hadamardWord._proof_1
#print axioms ExactFourierCircuits.TypedKernelWords.hadamardWord._proof_2
#print axioms ExactFourierCircuits.TypedKernelWords.hadamardWord._proof_3
#print axioms ExactFourierCircuits.TypedKernelWords.hadamardWord.eq_1
#print axioms ExactFourierCircuits.TypedKernelWords.hadamardWord_calls
#print axioms ExactFourierCircuits.TypedKernelWords.hadamardWord_matrix
#print axioms ExactFourierCircuits.TypedKernelWords.inverseWord
#print axioms ExactFourierCircuits.TypedKernelWords.inverseWord.eq_1
#print axioms ExactFourierCircuits.TypedKernelWords.inverseWord_calls
#print axioms ExactFourierCircuits.TypedKernelWords.inverseWord_matrix
#print axioms ExactFourierCircuits.TypedKernelWords.isMonomial_reindex
#print axioms ExactFourierCircuits.TypedKernelWords.relabelStep
#print axioms ExactFourierCircuits.TypedKernelWords.relabelStep.match_1
#print axioms ExactFourierCircuits.TypedKernelWords.relabelStep_calls
#print axioms ExactFourierCircuits.TypedKernelWords.relabelStep_matrix
#print axioms ExactFourierCircuits.TypedKernelWords.relabelWord
#print axioms ExactFourierCircuits.TypedKernelWords.relabelWord.eq_1
#print axioms ExactFourierCircuits.TypedKernelWords.relabelWord_calls
#print axioms ExactFourierCircuits.TypedKernelWords.relabelWord_matrix
#print axioms ExactFourierCircuits.TypedKernelWords.shearWord
#print axioms ExactFourierCircuits.TypedKernelWords.shearWord._proof_1
#print axioms ExactFourierCircuits.TypedKernelWords.shearWord._proof_10
#print axioms ExactFourierCircuits.TypedKernelWords.shearWord._proof_11
#print axioms ExactFourierCircuits.TypedKernelWords.shearWord._proof_12
#print axioms ExactFourierCircuits.TypedKernelWords.shearWord._proof_2
#print axioms ExactFourierCircuits.TypedKernelWords.shearWord._proof_3
#print axioms ExactFourierCircuits.TypedKernelWords.shearWord._proof_4
#print axioms ExactFourierCircuits.TypedKernelWords.shearWord._proof_5
#print axioms ExactFourierCircuits.TypedKernelWords.shearWord._proof_6
#print axioms ExactFourierCircuits.TypedKernelWords.shearWord._proof_7
#print axioms ExactFourierCircuits.TypedKernelWords.shearWord._proof_8
#print axioms ExactFourierCircuits.TypedKernelWords.shearWord._proof_9
#print axioms ExactFourierCircuits.TypedKernelWords.shearWord.eq_1
#print axioms ExactFourierCircuits.TypedKernelWords.shearWord_calls
#print axioms ExactFourierCircuits.TypedKernelWords.shearWord_matrix
#print axioms ExactFourierCircuits.TypedKernelWords.swap_isMonomial
#print axioms ExactFourierCircuits.TypedKernelWords.wordCalls_append
#print axioms ExactFourierCircuits.TypedKernelWords.wordMatrix_append
#print axioms ExactFourierCircuits.TypedKernelWords.wordMatrix_pair
#print axioms ExactFourierCircuits.TypedKernelWords.wordMatrix_singleton
#print axioms OAI.ExactFourier.WordStep.calls.eq_1
#print axioms OAI.ExactFourier.WordStep.calls.eq_2
#print axioms OAI.ExactFourier.WordStep.matrix.eq_1
#print axioms OAI.ExactFourier.WordStep.matrix.eq_2
#print axioms OAI.ExactFourier.WordStep.monomial.congr_simp
#print axioms OAI.ExactFourier.embeddedCall.eq_1
#print axioms OAI.ExactFourier.wordCalls.eq_1
#print axioms OAI.ExactFourier.wordMatrix.eq_1

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.TypedKernelWords.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

import TensorWords
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.DirectionalWords.directionalC.eq_1
#print axioms ExactFourierCircuits.TensorWords.binaryC
#print axioms ExactFourierCircuits.TensorWords.binaryC.eq_1
#print axioms ExactFourierCircuits.TensorWords.binaryC_apply
#print axioms ExactFourierCircuits.TensorWords.binary_flip_eq
#print axioms ExactFourierCircuits.TensorWords.bitEquiv
#print axioms ExactFourierCircuits.TensorWords.bitEquiv._proof_1
#print axioms ExactFourierCircuits.TensorWords.compile_ordinary_tensor
#print axioms ExactFourierCircuits.TensorWords.embedStep
#print axioms ExactFourierCircuits.TensorWords.embedStep._proof_1
#print axioms ExactFourierCircuits.TensorWords.embedStep.eq_1
#print axioms ExactFourierCircuits.TensorWords.embedStep.eq_2
#print axioms ExactFourierCircuits.TensorWords.embedStep.match_1
#print axioms ExactFourierCircuits.TensorWords.embedStep_calls
#print axioms ExactFourierCircuits.TensorWords.embedStep_matrix
#print axioms ExactFourierCircuits.TensorWords.embeddedWord
#print axioms ExactFourierCircuits.TensorWords.embeddedWord.eq_1
#print axioms ExactFourierCircuits.TensorWords.embeddedWord_blocks
#print axioms ExactFourierCircuits.TensorWords.embeddedWord_calls
#print axioms ExactFourierCircuits.TensorWords.embeddedWord_matrix
#print axioms ExactFourierCircuits.TensorWords.embeddedWord_off
#print axioms ExactFourierCircuits.TensorWords.embeddedWord_on
#print axioms ExactFourierCircuits.TensorWords.ordinaryTensorWord
#print axioms ExactFourierCircuits.TensorWords.ordinaryTensorWord.eq_1
#print axioms ExactFourierCircuits.TensorWords.ordinaryTensorWord_calls
#print axioms ExactFourierCircuits.TensorWords.ordinaryTensorWord_matrix
#print axioms ExactFourierCircuits.TensorWords.parallelWord
#print axioms ExactFourierCircuits.TensorWords.parallelWord.eq_1
#print axioms ExactFourierCircuits.TensorWords.parallelWord_calls
#print axioms ExactFourierCircuits.TensorWords.parallelWord_matrix
#print axioms ExactFourierCircuits.TensorWords.parallelWord_matrix._simp_1_2
#print axioms ExactFourierCircuits.TensorWords.tensorBits
#print axioms ExactFourierCircuits.TensorWords.tensorBits.eq_1
#print axioms ExactFourierCircuits.TensorWords.tensorCoordinates_bridge
#print axioms ExactFourierCircuits.TensorWords.tensorRelabel
#print axioms ExactFourierCircuits.TensorWords.tensorRelabel.eq_1
#print axioms ExactFourierCircuits.TensorWords.unitAxesWord
#print axioms ExactFourierCircuits.TensorWords.unitAxesWord.eq_1
#print axioms ExactFourierCircuits.TensorWords.unitAxesWord_calls
#print axioms ExactFourierCircuits.TensorWords.unitAxesWord_matrix
#print axioms ExactFourierCircuits.TensorWords.unitAxisWord
#print axioms ExactFourierCircuits.TensorWords.unitAxisWord_calls
#print axioms ExactFourierCircuits.TensorWords.unitAxisWord_matrix
#print axioms ExactFourierCircuits.TensorWords.unitDirection
#print axioms ExactFourierCircuits.TensorWords.unitDirection_pivot
#print axioms ExactFourierCircuits.TensorWords.unit_axes_product
#print axioms ExactFourierCircuits.TensorWords.unit_axes_product._simp_1_1
#print axioms ExactFourierCircuits.TensorWords.unit_axis_matrix
#print axioms ExactFourierCircuits.TensorWords.unit_axis_matrix._simp_1_1
#print axioms ExactFourierCircuits.TensorWords.wordCalls_flatten
#print axioms ExactFourierCircuits.TensorWords.wordMatrix_cons
#print axioms ExactFourierCircuits.TensorWords.wordMatrix_flatten
#print axioms ZMod.finEquiv.congr_simp

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.TensorWords.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

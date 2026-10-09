import UniformNativeResidualBasis
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.ColumnSchedule.columnResidualBasis.congr_simp
#print axioms ExactFourierCircuits.ColumnSchedule.edgeColumns.eq_1
#print axioms ExactFourierCircuits.ColumnSchedule.edgeColumns.eq_2
#print axioms ExactFourierCircuits.FrameWords.signedFrameList.congr_simp
#print axioms ExactFourierCircuits.UniformFixedNetwork.edgeInverse.eq_1
#print axioms ExactFourierCircuits.UniformFixedNetwork.edgeInverse.eq_2
#print axioms ExactFourierCircuits.UniformFixedNetwork.edgeVectors.eq_1
#print axioms ExactFourierCircuits.UniformFixedNetwork.edgeVectors.eq_2
#print axioms ExactFourierCircuits.UniformNativeResidualBasis.basisWord
#print axioms ExactFourierCircuits.UniformNativeResidualBasis.basisWord.eq_1
#print axioms ExactFourierCircuits.UniformNativeResidualBasis.basisWord_matrix
#print axioms ExactFourierCircuits.UniformNativeResidualBasis.binaryAction_injective
#print axioms ExactFourierCircuits.UniformNativeResidualBasis.groups_character
#print axioms ExactFourierCircuits.UniformNativeResidualBasis.role_basisWord_matrix

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformNativeResidualBasis.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

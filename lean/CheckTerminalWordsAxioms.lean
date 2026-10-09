import TerminalWords
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.TerminalWords.Point
#print axioms ExactFourierCircuits.TerminalWords.Role
#print axioms ExactFourierCircuits.TerminalWords.bankCoordinates
#print axioms ExactFourierCircuits.TerminalWords.bankCoordinates._proof_1
#print axioms ExactFourierCircuits.TerminalWords.coordinateWord
#print axioms ExactFourierCircuits.TerminalWords.coordinateWord._proof_1
#print axioms ExactFourierCircuits.TerminalWords.coordinateWord.eq_1
#print axioms ExactFourierCircuits.TerminalWords.coordinateWord_action
#print axioms ExactFourierCircuits.TerminalWords.coordinateWord_calls
#print axioms ExactFourierCircuits.TerminalWords.copyCoordinates
#print axioms ExactFourierCircuits.TerminalWords.copyCoordinates.eq_1
#print axioms ExactFourierCircuits.TerminalWords.corrected_endpoint_word
#print axioms ExactFourierCircuits.TerminalWords.correctionWord
#print axioms ExactFourierCircuits.TerminalWords.correctionWord.eq_1
#print axioms ExactFourierCircuits.TerminalWords.correctionWord_action
#print axioms ExactFourierCircuits.TerminalWords.correctionWord_calls
#print axioms ExactFourierCircuits.TerminalWords.correctionWord_matrix
#print axioms ExactFourierCircuits.TerminalWords.correctionWord_monomial
#print axioms ExactFourierCircuits.TerminalWords.correctionWord_unit
#print axioms ExactFourierCircuits.TerminalWords.exchangeEquiv
#print axioms ExactFourierCircuits.TerminalWords.exchangeEquiv_apply
#print axioms ExactFourierCircuits.TerminalWords.exchangeMatrix
#print axioms ExactFourierCircuits.TerminalWords.exchangeMatrix.eq_1
#print axioms ExactFourierCircuits.TerminalWords.exchangeMatrix_action
#print axioms ExactFourierCircuits.TerminalWords.exchangeMatrix_monomial
#print axioms ExactFourierCircuits.TerminalWords.exchangePoint
#print axioms ExactFourierCircuits.TerminalWords.exchangePoint.eq_1
#print axioms ExactFourierCircuits.TerminalWords.exchangePoint.eq_2
#print axioms ExactFourierCircuits.TerminalWords.exchangePoint_involutive
#print axioms ExactFourierCircuits.TerminalWords.exchangeSign
#print axioms ExactFourierCircuits.TerminalWords.exchangeSign.eq_1
#print axioms ExactFourierCircuits.TerminalWords.exchangeSign.eq_2
#print axioms ExactFourierCircuits.TerminalWords.exchangeSign_nonzero
#print axioms ExactFourierCircuits.TerminalWords.finiteBankDirection
#print axioms ExactFourierCircuits.TerminalWords.finiteBankDirection._proof_1
#print axioms ExactFourierCircuits.TerminalWords.finiteBankDirection.eq_1
#print axioms ExactFourierCircuits.TerminalWords.finiteBankDirection_norm
#print axioms ExactFourierCircuits.TerminalWords.master_terminal_bridge
#print axioms ExactFourierCircuits.TerminalWords.master_terminal_bridge_of_endpoint
#print axioms ExactFourierCircuits.TerminalWords.master_terminal_calls
#print axioms ExactFourierCircuits.TerminalWords.matrix_eq_of_mulVec
#print axioms ExactFourierCircuits.TerminalWords.monomial
#print axioms ExactFourierCircuits.TerminalWords.monomial.eq_1
#print axioms ExactFourierCircuits.TerminalWords.monomial_apply
#print axioms ExactFourierCircuits.TerminalWords.monomial_isMonomial
#print axioms ExactFourierCircuits.TerminalWords.ordinaryMatrix
#print axioms ExactFourierCircuits.TerminalWords.ordinaryMatrix.eq_1
#print axioms ExactFourierCircuits.TerminalWords.ordinaryMatrix_role_apply
#print axioms ExactFourierCircuits.TerminalWords.ordinaryWord
#print axioms ExactFourierCircuits.TerminalWords.ordinaryWord.eq_1
#print axioms ExactFourierCircuits.TerminalWords.ordinaryWord_action
#print axioms ExactFourierCircuits.TerminalWords.ordinaryWord_binary_action
#print axioms ExactFourierCircuits.TerminalWords.ordinaryWord_calls
#print axioms ExactFourierCircuits.TerminalWords.ordinaryWord_matrix
#print axioms ExactFourierCircuits.TerminalWords.pack
#print axioms ExactFourierCircuits.TerminalWords.pack.eq_1
#print axioms ExactFourierCircuits.TerminalWords.pack_at
#print axioms ExactFourierCircuits.TerminalWords.pack_binaryValues
#print axioms ExactFourierCircuits.TerminalWords.pack_surjective
#print axioms ExactFourierCircuits.TerminalWords.packedPerm
#print axioms ExactFourierCircuits.TerminalWords.packedPerm.eq_1
#print axioms ExactFourierCircuits.TerminalWords.points
#print axioms ExactFourierCircuits.TerminalWords.signedExchange
#print axioms ExactFourierCircuits.TerminalWords.signedExchange.eq_1
#print axioms ExactFourierCircuits.TerminalWords.stateArrays
#print axioms ExactFourierCircuits.TerminalWords.stateArrays.eq_1
#print axioms ExactFourierCircuits.TerminalWords.stateArrays_ordinary
#print axioms ExactFourierCircuits.TerminalWords.translateY
#print axioms ExactFourierCircuits.TerminalWords.translateY.eq_1
#print axioms ExactFourierCircuits.TerminalWords.translateY.eq_2
#print axioms ExactFourierCircuits.TerminalWords.translateYEquiv
#print axioms ExactFourierCircuits.TerminalWords.translateYEquiv_apply
#print axioms ExactFourierCircuits.TerminalWords.translateY_involutive
#print axioms ExactFourierCircuits.TerminalWords.translatedY
#print axioms ExactFourierCircuits.TerminalWords.translatedY.eq_1
#print axioms ExactFourierCircuits.TerminalWords.translationMatrix
#print axioms ExactFourierCircuits.TerminalWords.translationMatrix.eq_1
#print axioms ExactFourierCircuits.TerminalWords.translationMatrix_action
#print axioms ExactFourierCircuits.TerminalWords.translationMatrix_monomial
#print axioms ExactFourierCircuits.TerminalWords.triple_corrected_endpoint_word
#print axioms ExactFourierCircuits.TerminalWords.triple_master_terminal_bridge
#print axioms ExactFourierCircuits.TerminalWords.values
#print axioms ExactFourierCircuits.TerminalWords.values._proof_1
#print axioms ExactFourierCircuits.TerminalWords.values.eq_1
#print axioms ExactFourierCircuits.TerminalWords.values.eq_2
#print axioms ExactFourierCircuits.TerminalWords.values.match_1

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.TerminalWords.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

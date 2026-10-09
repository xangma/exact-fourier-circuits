import FrameSpectrum
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.FrameSpectrum.Array
#print axioms ExactFourierCircuits.FrameSpectrum.I_pow_four
#print axioms ExactFourierCircuits.FrameSpectrum.I_pow_mod_four
#print axioms ExactFourierCircuits.FrameSpectrum.Operator
#print axioms ExactFourierCircuits.FrameSpectrum.binarySign
#print axioms ExactFourierCircuits.FrameSpectrum.binarySign.eq_1
#print axioms ExactFourierCircuits.FrameSpectrum.binarySign_add
#print axioms ExactFourierCircuits.FrameSpectrum.binarySign_one
#print axioms ExactFourierCircuits.FrameSpectrum.binarySign_phase
#print axioms ExactFourierCircuits.FrameSpectrum.binarySign_zero
#print axioms ExactFourierCircuits.FrameSpectrum.binary_cases
#print axioms ExactFourierCircuits.FrameSpectrum.cardinal_ne_zero
#print axioms ExactFourierCircuits.FrameSpectrum.character
#print axioms ExactFourierCircuits.FrameSpectrum.character.eq_1
#print axioms ExactFourierCircuits.FrameSpectrum.character_add
#print axioms ExactFourierCircuits.FrameSpectrum.character_at_zero
#print axioms ExactFourierCircuits.FrameSpectrum.character_comm
#print axioms ExactFourierCircuits.FrameSpectrum.character_expansion
#print axioms ExactFourierCircuits.FrameSpectrum.character_pair_sum
#print axioms ExactFourierCircuits.FrameSpectrum.character_pair_sum._simp_1_1
#print axioms ExactFourierCircuits.FrameSpectrum.character_sum
#print axioms ExactFourierCircuits.FrameSpectrum.character_sum_nonzero
#print axioms ExactFourierCircuits.FrameSpectrum.character_zero
#print axioms ExactFourierCircuits.FrameSpectrum.coordinate_word_standard
#print axioms ExactFourierCircuits.FrameSpectrum.directionalMap
#print axioms ExactFourierCircuits.FrameSpectrum.directionalMap._proof_1
#print axioms ExactFourierCircuits.FrameSpectrum.directionalMap._proof_2
#print axioms ExactFourierCircuits.FrameSpectrum.directional_character
#print axioms ExactFourierCircuits.FrameSpectrum.directional_inverse
#print axioms ExactFourierCircuits.FrameSpectrum.directional_square
#print axioms ExactFourierCircuits.FrameSpectrum.edgeSign
#print axioms ExactFourierCircuits.FrameSpectrum.edgeSign.eq_1
#print axioms ExactFourierCircuits.FrameSpectrum.frameEquiv
#print axioms ExactFourierCircuits.FrameSpectrum.frameEquiv._proof_1
#print axioms ExactFourierCircuits.FrameSpectrum.frameEquiv._proof_2
#print axioms ExactFourierCircuits.FrameSpectrum.frameEquiv._proof_3
#print axioms ExactFourierCircuits.FrameSpectrum.frameEquiv._proof_4
#print axioms ExactFourierCircuits.FrameSpectrum.frameMap
#print axioms ExactFourierCircuits.FrameSpectrum.frameMap._proof_1
#print axioms ExactFourierCircuits.FrameSpectrum.frameMap._proof_2
#print axioms ExactFourierCircuits.FrameSpectrum.frameMap_character
#print axioms ExactFourierCircuits.FrameSpectrum.frameMap_character._simp_1_1
#print axioms ExactFourierCircuits.FrameSpectrum.frameMap_character._simp_1_2
#print axioms ExactFourierCircuits.FrameSpectrum.frameMap_character._simp_1_3
#print axioms ExactFourierCircuits.FrameSpectrum.frameMap_character._simp_1_4
#print axioms ExactFourierCircuits.FrameSpectrum.frameMap_character._simp_1_5
#print axioms ExactFourierCircuits.FrameSpectrum.frameMap_character._simp_1_6
#print axioms ExactFourierCircuits.FrameSpectrum.frameMap_character._simp_1_7
#print axioms ExactFourierCircuits.FrameSpectrum.frameMap_character._simp_1_8
#print axioms ExactFourierCircuits.FrameSpectrum.frameMap_comp
#print axioms ExactFourierCircuits.FrameSpectrum.frameMap_inverse
#print axioms ExactFourierCircuits.FrameSpectrum.frameMap_zero
#print axioms ExactFourierCircuits.FrameSpectrum.frame_ratio_signedWord
#print axioms ExactFourierCircuits.FrameSpectrum.inverseDirectionalMap
#print axioms ExactFourierCircuits.FrameSpectrum.inverseDirectionalMap._proof_1
#print axioms ExactFourierCircuits.FrameSpectrum.inverseDirectionalMap._proof_2
#print axioms ExactFourierCircuits.FrameSpectrum.inverse_directional_character
#print axioms ExactFourierCircuits.FrameSpectrum.inverse_directional_translation
#print axioms ExactFourierCircuits.FrameSpectrum.inverse_kernel_phase
#print axioms ExactFourierCircuits.FrameSpectrum.kernel_phase
#print axioms ExactFourierCircuits.FrameSpectrum.lineExponent
#print axioms ExactFourierCircuits.FrameSpectrum.norm_one_weightModFour
#print axioms ExactFourierCircuits.FrameSpectrum.operator_eq_of_characters
#print axioms ExactFourierCircuits.FrameSpectrum.perpExponent
#print axioms ExactFourierCircuits.FrameSpectrum.phase
#print axioms ExactFourierCircuits.FrameSpectrum.phase.eq_1
#print axioms ExactFourierCircuits.FrameSpectrum.phaseMap
#print axioms ExactFourierCircuits.FrameSpectrum.phaseMap._proof_1
#print axioms ExactFourierCircuits.FrameSpectrum.phaseMap._proof_2
#print axioms ExactFourierCircuits.FrameSpectrum.phase_add
#print axioms ExactFourierCircuits.FrameSpectrum.phase_finset_sum
#print axioms ExactFourierCircuits.FrameSpectrum.phase_natCast
#print axioms ExactFourierCircuits.FrameSpectrum.phase_ne_zero
#print axioms ExactFourierCircuits.FrameSpectrum.phase_neg
#print axioms ExactFourierCircuits.FrameSpectrum.phase_neg_one
#print axioms ExactFourierCircuits.FrameSpectrum.phase_one
#print axioms ExactFourierCircuits.FrameSpectrum.phase_zero
#print axioms ExactFourierCircuits.FrameSpectrum.signedMap
#print axioms ExactFourierCircuits.FrameSpectrum.signedMap.eq_1
#print axioms ExactFourierCircuits.FrameSpectrum.signedMap_character
#print axioms ExactFourierCircuits.FrameSpectrum.signedMap_unit
#print axioms ExactFourierCircuits.FrameSpectrum.signedWord
#print axioms ExactFourierCircuits.FrameSpectrum.signedWord._f
#print axioms ExactFourierCircuits.FrameSpectrum.signedWord._sunfold
#print axioms ExactFourierCircuits.FrameSpectrum.signedWord._unsafe_rec
#print axioms ExactFourierCircuits.FrameSpectrum.signedWord.eq_1
#print axioms ExactFourierCircuits.FrameSpectrum.signedWord.eq_2
#print axioms ExactFourierCircuits.FrameSpectrum.signedWord.eq_def
#print axioms ExactFourierCircuits.FrameSpectrum.signedWord.match_1
#print axioms ExactFourierCircuits.FrameSpectrum.signedWord_character
#print axioms ExactFourierCircuits.FrameSpectrum.signedWord_frame
#print axioms ExactFourierCircuits.FrameSpectrum.signedWords_same_projection
#print axioms ExactFourierCircuits.FrameSpectrum.signed_projection_phase
#print axioms ExactFourierCircuits.FrameSpectrum.terminal_frame_ratio
#print axioms ExactFourierCircuits.FrameSpectrum.terminal_weight_ratio
#print axioms ExactFourierCircuits.FrameSpectrum.translateMap
#print axioms ExactFourierCircuits.FrameSpectrum.translateMap._proof_1
#print axioms ExactFourierCircuits.FrameSpectrum.translateMap._proof_2
#print axioms ExactFourierCircuits.FrameSpectrum.translate_character
#print axioms ExactFourierCircuits.FrameSpectrum.unit_frameProjection
#print axioms ExactFourierCircuits.FrameSpectrum.vec_add_self
#print axioms ExactFourierCircuits.FrameSpectrum.walsh
#print axioms ExactFourierCircuits.FrameSpectrum.walsh._proof_1
#print axioms ExactFourierCircuits.FrameSpectrum.walsh.congr_simp
#print axioms ExactFourierCircuits.FrameSpectrum.walsh.eq_1
#print axioms ExactFourierCircuits.FrameSpectrum.walshMap
#print axioms ExactFourierCircuits.FrameSpectrum.walshMap._proof_1
#print axioms ExactFourierCircuits.FrameSpectrum.walshMap._proof_2
#print axioms ExactFourierCircuits.FrameSpectrum.walsh_character
#print axioms ExactFourierCircuits.FrameSpectrum.walsh_square
#print axioms ExactFourierCircuits.FrameSpectrum.weightModFour_unit

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.FrameSpectrum.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

import TripleStageAction
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.FrameSpectrum.lineExponent.eq_1
#print axioms ExactFourierCircuits.FrameSpectrum.perpExponent.eq_1
#print axioms ExactFourierCircuits.FramedScheduleWords.Label.exponent.eq_1
#print axioms ExactFourierCircuits.FramedScheduleWords.Label.vectors.eq_1
#print axioms ExactFourierCircuits.GateFrames.labelOfBasis.congr_simp
#print axioms ExactFourierCircuits.NetworkTerminal.sinkFrames.eq_1
#print axioms ExactFourierCircuits.NetworkTerminal.sourceInverse.eq_1
#print axioms ExactFourierCircuits.TripleStageAction.Arrays
#print axioms ExactFourierCircuits.TripleStageAction.Aux
#print axioms ExactFourierCircuits.TripleStageAction.Role
#print axioms ExactFourierCircuits.TripleStageAction.State
#print axioms ExactFourierCircuits.TripleStageAction.cancel_of_exponents
#print axioms ExactFourierCircuits.TripleStageAction.consecutive_cancel
#print axioms ExactFourierCircuits.TripleStageAction.consecutive_exponents
#print axioms ExactFourierCircuits.TripleStageAction.consecutive_spaces
#print axioms ExactFourierCircuits.TripleStageAction.consecutive_spaces._proof_1_3
#print axioms ExactFourierCircuits.TripleStageAction.consecutive_spaces._simp_1_1
#print axioms ExactFourierCircuits.TripleStageAction.consecutive_spaces._simp_1_2
#print axioms ExactFourierCircuits.TripleStageAction.corrected_stages_endpoint
#print axioms ExactFourierCircuits.TripleStageAction.exchanged
#print axioms ExactFourierCircuits.TripleStageAction.exchanged.eq_1
#print axioms ExactFourierCircuits.TripleStageAction.exchanged.eq_2
#print axioms ExactFourierCircuits.TripleStageAction.exchanged_arrays
#print axioms ExactFourierCircuits.TripleStageAction.final_auxiliary_exponent
#print axioms ExactFourierCircuits.TripleStageAction.final_auxiliary_exponent._proof_1_1
#print axioms ExactFourierCircuits.TripleStageAction.final_exponents
#print axioms ExactFourierCircuits.TripleStageAction.framedStage
#print axioms ExactFourierCircuits.TripleStageAction.framed_stages
#print axioms ExactFourierCircuits.TripleStageAction.framed_stages_endpoint
#print axioms ExactFourierCircuits.TripleStageAction.frames
#print axioms ExactFourierCircuits.TripleStageAction.frames.eq_1
#print axioms ExactFourierCircuits.TripleStageAction.fullLabel
#print axioms ExactFourierCircuits.TripleStageAction.fullLabel._proof_1
#print axioms ExactFourierCircuits.TripleStageAction.fullLabel.eq_1
#print axioms ExactFourierCircuits.TripleStageAction.incoming
#print axioms ExactFourierCircuits.TripleStageAction.incoming._proof_1
#print axioms ExactFourierCircuits.TripleStageAction.incoming._proof_2
#print axioms ExactFourierCircuits.TripleStageAction.incoming.congr_simp
#print axioms ExactFourierCircuits.TripleStageAction.incoming.eq_1
#print axioms ExactFourierCircuits.TripleStageAction.incoming.eq_2
#print axioms ExactFourierCircuits.TripleStageAction.incoming.match_1
#print axioms ExactFourierCircuits.TripleStageAction.initial_auxiliary_exponent
#print axioms ExactFourierCircuits.TripleStageAction.initial_exponents
#print axioms ExactFourierCircuits.TripleStageAction.inverseFrames
#print axioms ExactFourierCircuits.TripleStageAction.inverseFrames.eq_1
#print axioms ExactFourierCircuits.TripleStageAction.inverse_frames
#print axioms ExactFourierCircuits.TripleStageAction.label_exponent_bot
#print axioms ExactFourierCircuits.TripleStageAction.label_exponent_line
#print axioms ExactFourierCircuits.TripleStageAction.label_exponent_perp
#print axioms ExactFourierCircuits.TripleStageAction.label_exponent_top
#print axioms ExactFourierCircuits.TripleStageAction.outgoing
#print axioms ExactFourierCircuits.TripleStageAction.outgoing.congr_simp
#print axioms ExactFourierCircuits.TripleStageAction.outgoing.eq_1
#print axioms ExactFourierCircuits.TripleStageAction.outgoing.eq_2
#print axioms ExactFourierCircuits.TripleStageAction.scalarStage
#print axioms ExactFourierCircuits.TripleStageAction.scalarStage._proof_1
#print axioms ExactFourierCircuits.TripleStageAction.scalarStage.eq_1
#print axioms ExactFourierCircuits.TripleStageAction.scalarStage.eq_2
#print axioms ExactFourierCircuits.TripleStageAction.scalar_stages
#print axioms ExactFourierCircuits.TripleStageAction.sink_frames_arrays
#print axioms ExactFourierCircuits.TripleStageAction.source_inverse_arrays
#print axioms ExactFourierCircuits.TripleStageAction.stateArrays
#print axioms ExactFourierCircuits.TripleStageAction.stateArrays.eq_1
#print axioms ExactFourierCircuits.TripleStageAction.stateArrays.eq_2
#print axioms ExactFourierCircuits.TripleStageAction.zeroLabel
#print axioms ExactFourierCircuits.TripleStageAction.zeroLabel._proof_1
#print axioms ExactFourierCircuits.TripleStageAction.zeroLabel.eq_1

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.TripleStageAction.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

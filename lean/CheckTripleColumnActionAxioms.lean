import TripleColumnAction
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.ColumnSchedule.columnSpace.eq_1
#print axioms ExactFourierCircuits.TripleColumnAction.Arrays
#print axioms ExactFourierCircuits.TripleColumnAction.Role
#print axioms ExactFourierCircuits.TripleColumnAction.State
#print axioms ExactFourierCircuits.TripleColumnAction.cancel_of_exponents
#print axioms ExactFourierCircuits.TripleColumnAction.columns_top_exponent
#print axioms ExactFourierCircuits.TripleColumnAction.consecutive_cancel
#print axioms ExactFourierCircuits.TripleColumnAction.consecutive_exponents
#print axioms ExactFourierCircuits.TripleColumnAction.consecutive_spaces
#print axioms ExactFourierCircuits.TripleColumnAction.corrected_stages_endpoint
#print axioms ExactFourierCircuits.TripleColumnAction.endpoint
#print axioms ExactFourierCircuits.TripleColumnAction.exchanged
#print axioms ExactFourierCircuits.TripleColumnAction.exchanged.eq_1
#print axioms ExactFourierCircuits.TripleColumnAction.exchanged.eq_2
#print axioms ExactFourierCircuits.TripleColumnAction.exchanged_arrays
#print axioms ExactFourierCircuits.TripleColumnAction.final_auxiliary_exponent
#print axioms ExactFourierCircuits.TripleColumnAction.final_auxiliary_exponent._proof_1_1
#print axioms ExactFourierCircuits.TripleColumnAction.final_exponents
#print axioms ExactFourierCircuits.TripleColumnAction.framedStage
#print axioms ExactFourierCircuits.TripleColumnAction.framed_stages
#print axioms ExactFourierCircuits.TripleColumnAction.framed_stages_endpoint
#print axioms ExactFourierCircuits.TripleColumnAction.frames
#print axioms ExactFourierCircuits.TripleColumnAction.frames.eq_1
#print axioms ExactFourierCircuits.TripleColumnAction.globalDirection
#print axioms ExactFourierCircuits.TripleColumnAction.incoming
#print axioms ExactFourierCircuits.TripleColumnAction.incoming.congr_simp
#print axioms ExactFourierCircuits.TripleColumnAction.incoming.eq_1
#print axioms ExactFourierCircuits.TripleColumnAction.initial_auxiliary_exponent
#print axioms ExactFourierCircuits.TripleColumnAction.initial_exponents
#print axioms ExactFourierCircuits.TripleColumnAction.inverseFrames
#print axioms ExactFourierCircuits.TripleColumnAction.inverseFrames.eq_1
#print axioms ExactFourierCircuits.TripleColumnAction.lineExponent
#print axioms ExactFourierCircuits.TripleColumnAction.lineExponent.eq_1
#print axioms ExactFourierCircuits.TripleColumnAction.outgoing
#print axioms ExactFourierCircuits.TripleColumnAction.outgoing.congr_simp
#print axioms ExactFourierCircuits.TripleColumnAction.outgoing.eq_1
#print axioms ExactFourierCircuits.TripleColumnAction.perpExponent
#print axioms ExactFourierCircuits.TripleColumnAction.perpExponent.eq_1
#print axioms ExactFourierCircuits.TripleColumnAction.scalarStage
#print axioms ExactFourierCircuits.TripleColumnAction.scalarStage._proof_1
#print axioms ExactFourierCircuits.TripleColumnAction.scalarStage._proof_2
#print axioms ExactFourierCircuits.TripleColumnAction.scalarStage.eq_1
#print axioms ExactFourierCircuits.TripleColumnAction.scalarStage.eq_2
#print axioms ExactFourierCircuits.TripleColumnAction.scalarStage.match_1
#print axioms ExactFourierCircuits.TripleColumnAction.scalar_stages
#print axioms ExactFourierCircuits.TripleColumnAction.sinkFrames
#print axioms ExactFourierCircuits.TripleColumnAction.sinkFrames.eq_1
#print axioms ExactFourierCircuits.TripleColumnAction.sink_frames_arrays
#print axioms ExactFourierCircuits.TripleColumnAction.sourceInverse
#print axioms ExactFourierCircuits.TripleColumnAction.sourceInverse.eq_1
#print axioms ExactFourierCircuits.TripleColumnAction.source_inverse_arrays
#print axioms ExactFourierCircuits.TripleColumnAction.stateArrays
#print axioms ExactFourierCircuits.TripleColumnAction.stateArrays.eq_1
#print axioms ExactFourierCircuits.TripleColumnAction.stateArrays.eq_2

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.TripleColumnAction.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

import UniformCalendarRenderCorrespondence
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformCalendarRenderCorrespondence.calendar_tick
#print axioms ExactFourierCircuits.UniformCalendarRenderCorrespondence.calendar_tick._abel_1_12
#print axioms ExactFourierCircuits.UniformCalendarRenderCorrespondence.calendar_tick._abel_1_5
#print axioms ExactFourierCircuits.UniformCalendarRenderCorrespondence.calendar_tick._abel_1_7
#print axioms ExactFourierCircuits.UniformCalendarRenderCorrespondence.calendar_tick._proof_1_10
#print axioms ExactFourierCircuits.UniformCalendarRenderCorrespondence.calendar_tick._proof_1_11
#print axioms ExactFourierCircuits.UniformCalendarRenderCorrespondence.calendar_tick._proof_1_13
#print axioms ExactFourierCircuits.UniformCalendarRenderCorrespondence.calendar_tick._proof_1_6
#print axioms ExactFourierCircuits.UniformCalendarRenderCorrespondence.calendar_tick._proof_1_8
#print axioms ExactFourierCircuits.UniformCalendarRenderCorrespondence.calendar_tick._proof_1_9
#print axioms ExactFourierCircuits.UniformCalendarRenderCorrespondence.correction_tick
#print axioms ExactFourierCircuits.UniformCalendarRenderCorrespondence.embed_refl
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.correctionPieces.eq_1
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.directPiece.eq_1
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnion.Event.width.eq_1
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnion.Event.width.eq_2

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformCalendarRenderCorrespondence.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

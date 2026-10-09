import UniformCalendarRenderPlan
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.calendar
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.calendar._f
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.calendar._sunfold
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.calendar._unsafe_rec
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.calendar.congr_simp
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.calendar.eq_1
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.calendar.eq_2
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.calendar.eq_def
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.calendar.match_1
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.calendar_inactive
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.calendar_inactive._proof_1_1
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.calendar_inactive._proof_1_2
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.correctionPieces
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.correctionPieces.congr_simp
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.correction_descriptors
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.descriptors
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.directPiece
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.directPiece._proof_1
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.directPiece._proof_2
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.directPiece.congr_simp
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.pairPiece
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.pairPiece._proof_1
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.pairPiece.congr_simp
#print axioms ExactFourierCircuits.UniformCalendarRenderPlan.pairPiece.eq_1

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformCalendarRenderPlan.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

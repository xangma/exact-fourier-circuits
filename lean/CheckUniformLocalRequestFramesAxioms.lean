import UniformLocalRequestFrames
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformLocalRequestFrames.Within
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.Within._sparseCasesOn_1
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.Within._sparseCasesOn_1.else_eq
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.Within.eq_1
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.Within.eq_2
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.Within.eq_3
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.Within.eq_4
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.Within.eq_5
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.Within.match_1
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.advanceWrites
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.advanceWrites.eq_1
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.advance_checked
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.advance_high
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.advance_high._proof_1_4
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.advance_high._simp_1_2
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.advance_high._simp_1_3
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.advance_nat
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.cursorWrites
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.cursorWrites.eq_1
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.cursor_checked
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.cursor_high
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.cursor_high._proof_1_4
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.cursor_high._simp_1_2
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.cursor_high._simp_1_3
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.cursor_nat
#print axioms ExactFourierCircuits.UniformLocalRequestFrames.outside_keeps

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformLocalRequestFrames.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

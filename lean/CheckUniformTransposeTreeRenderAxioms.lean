import UniformTransposeTreeRender
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformDirectLeafTransposeLayers.transposeLeafLayers.congr_simp
#print axioms ExactFourierCircuits.UniformTransposeRectangleRender.correction.congr_simp
#print axioms ExactFourierCircuits.UniformTransposeTreeRender.direct
#print axioms ExactFourierCircuits.UniformTransposeTreeRender.direct._proof_1
#print axioms ExactFourierCircuits.UniformTransposeTreeRender.direct.congr_simp
#print axioms ExactFourierCircuits.UniformTransposeTreeRender.direct_length
#print axioms ExactFourierCircuits.UniformTransposeTreeRender.direct_matrix
#print axioms ExactFourierCircuits.UniformTransposeTreeRender.direct_restricted
#print axioms ExactFourierCircuits.UniformTransposeTreeRender.frontParallel_restricted
#print axioms ExactFourierCircuits.UniformTransposeTreeRender.leading_restricted
#print axioms ExactFourierCircuits.UniformTransposeTreeRender.render
#print axioms ExactFourierCircuits.UniformTransposeTreeRender.render._f
#print axioms ExactFourierCircuits.UniformTransposeTreeRender.render._sunfold
#print axioms ExactFourierCircuits.UniformTransposeTreeRender.render._unsafe_rec
#print axioms ExactFourierCircuits.UniformTransposeTreeRender.render.congr_simp
#print axioms ExactFourierCircuits.UniformTransposeTreeRender.render.eq_1
#print axioms ExactFourierCircuits.UniformTransposeTreeRender.render.eq_2
#print axioms ExactFourierCircuits.UniformTransposeTreeRender.render.eq_def
#print axioms ExactFourierCircuits.UniformTransposeTreeRender.render.match_1
#print axioms ExactFourierCircuits.UniformTransposeTreeRender.render_length
#print axioms ExactFourierCircuits.UniformTransposeTreeRender.render_length._proof_1_4
#print axioms ExactFourierCircuits.UniformTransposeTreeRender.render_matrix
#print axioms ExactFourierCircuits.UniformTransposeTreeRender.render_restricted

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformTransposeTreeRender.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

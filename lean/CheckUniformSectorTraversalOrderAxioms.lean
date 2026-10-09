import UniformSectorTraversalOrder
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformSectorTraversalOrder.block_lex_ofFn
#print axioms ExactFourierCircuits.UniformSectorTraversalOrder.block_lex_sectorStates
#print axioms ExactFourierCircuits.UniformSectorTraversalOrder.foldl_output
#print axioms ExactFourierCircuits.UniformSectorTraversalOrder.lexOutcomes
#print axioms ExactFourierCircuits.UniformSectorTraversalOrder.lexOutcomes._f
#print axioms ExactFourierCircuits.UniformSectorTraversalOrder.lexOutcomes._sunfold
#print axioms ExactFourierCircuits.UniformSectorTraversalOrder.lexOutcomes._unsafe_rec
#print axioms ExactFourierCircuits.UniformSectorTraversalOrder.lexOutcomes.eq_1
#print axioms ExactFourierCircuits.UniformSectorTraversalOrder.lexOutcomes.eq_2
#print axioms ExactFourierCircuits.UniformSectorTraversalOrder.lexOutcomes.eq_def
#print axioms ExactFourierCircuits.UniformSectorTraversalOrder.lexOutcomes.match_1
#print axioms ExactFourierCircuits.UniformSectorTraversalOrder.run_output_reverse
#print axioms ExactFourierCircuits.UniformSectorTraversalOrder.run_sectorStates
#print axioms ExactFourierCircuits.UniformSectorTraversalOrder.traverse_output

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformSectorTraversalOrder.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

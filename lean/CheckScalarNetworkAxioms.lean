import ScalarNetwork
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.ScalarNetwork.Edge
#print axioms ExactFourierCircuits.ScalarNetwork.Edge.congr_simp
#print axioms ExactFourierCircuits.ScalarNetwork.G
#print axioms ExactFourierCircuits.ScalarNetwork.G.eq_1
#print axioms ExactFourierCircuits.ScalarNetwork.G.match_1
#print axioms ExactFourierCircuits.ScalarNetwork.J
#print axioms ExactFourierCircuits.ScalarNetwork.J.eq_1
#print axioms ExactFourierCircuits.ScalarNetwork.JV_entry
#print axioms ExactFourierCircuits.ScalarNetwork.JV_entry._simp_1_3
#print axioms ExactFourierCircuits.ScalarNetwork.R
#print axioms ExactFourierCircuits.ScalarNetwork.R.eq_1
#print axioms ExactFourierCircuits.ScalarNetwork.RG_entry
#print axioms ExactFourierCircuits.ScalarNetwork.Triple
#print axioms ExactFourierCircuits.ScalarNetwork.V
#print axioms ExactFourierCircuits.ScalarNetwork.V.eq_1
#print axioms ExactFourierCircuits.ScalarNetwork.coefficient
#print axioms ExactFourierCircuits.ScalarNetwork.coefficient._proof_1
#print axioms ExactFourierCircuits.ScalarNetwork.coefficient.congr_simp
#print axioms ExactFourierCircuits.ScalarNetwork.coefficient.eq_1
#print axioms ExactFourierCircuits.ScalarNetwork.composeMatrix
#print axioms ExactFourierCircuits.ScalarNetwork.composeMatrix.eq_1
#print axioms ExactFourierCircuits.ScalarNetwork.composeMatrix_mulVec
#print axioms ExactFourierCircuits.ScalarNetwork.incidence_identity
#print axioms ExactFourierCircuits.ScalarNetwork.incidence_identity._proof_1_3
#print axioms ExactFourierCircuits.ScalarNetwork.incidence_linear_identity
#print axioms ExactFourierCircuits.ScalarNetwork.instDecidableNeighboring
#print axioms ExactFourierCircuits.ScalarNetwork.instDecidableNeighboring._aux_1
#print axioms ExactFourierCircuits.ScalarNetwork.intersection_card_three_iff
#print axioms ExactFourierCircuits.ScalarNetwork.invocation_dirty_identity
#print axioms ExactFourierCircuits.ScalarNetwork.neighboring
#print axioms ExactFourierCircuits.ScalarNetwork.neighboring.congr_simp
#print axioms ExactFourierCircuits.ScalarNetwork.neighboring.eq_1
#print axioms ExactFourierCircuits.ScalarNetwork.neighboring_distinct
#print axioms ExactFourierCircuits.ScalarNetwork.neighboring_even
#print axioms ExactFourierCircuits.ScalarNetwork.neighboring_iff
#print axioms ExactFourierCircuits.ScalarNetwork.neighboring_iff._proof_1_1
#print axioms ExactFourierCircuits.ScalarNetwork.triple_card

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.ScalarNetwork.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

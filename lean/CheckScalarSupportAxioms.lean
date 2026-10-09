import ScalarSupport
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.ScalarSupport.G_nonzero
#print axioms ExactFourierCircuits.ScalarSupport.G_nonzero.match_1
#print axioms ExactFourierCircuits.ScalarSupport.G_support_card
#print axioms ExactFourierCircuits.ScalarSupport.Incidence
#print axioms ExactFourierCircuits.ScalarSupport.J_nonzero
#print axioms ExactFourierCircuits.ScalarSupport.J_nonzero._simp_1_1
#print axioms ExactFourierCircuits.ScalarSupport.J_support_card
#print axioms ExactFourierCircuits.ScalarSupport.J_support_equiv
#print axioms ExactFourierCircuits.ScalarSupport.J_support_equiv._proof_1
#print axioms ExactFourierCircuits.ScalarSupport.J_support_equiv._proof_2
#print axioms ExactFourierCircuits.ScalarSupport.J_support_equiv._proof_3
#print axioms ExactFourierCircuits.ScalarSupport.J_support_equiv._proof_4
#print axioms ExactFourierCircuits.ScalarSupport.R_nonzero
#print axioms ExactFourierCircuits.ScalarSupport.R_support_card
#print axioms ExactFourierCircuits.ScalarSupport.R_support_equiv
#print axioms ExactFourierCircuits.ScalarSupport.R_support_equiv._proof_1
#print axioms ExactFourierCircuits.ScalarSupport.R_support_equiv._proof_2
#print axioms ExactFourierCircuits.ScalarSupport.R_support_equiv._proof_3
#print axioms ExactFourierCircuits.ScalarSupport.R_support_equiv._proof_4
#print axioms ExactFourierCircuits.ScalarSupport.R_support_equiv._proof_5
#print axioms ExactFourierCircuits.ScalarSupport.R_support_equiv._proof_6
#print axioms ExactFourierCircuits.ScalarSupport.Support
#print axioms ExactFourierCircuits.ScalarSupport.V_nonzero
#print axioms ExactFourierCircuits.ScalarSupport.V_nonzero._simp_1_1
#print axioms ExactFourierCircuits.ScalarSupport.V_support_card
#print axioms ExactFourierCircuits.ScalarSupport.V_support_equiv
#print axioms ExactFourierCircuits.ScalarSupport.V_support_equiv._proof_1
#print axioms ExactFourierCircuits.ScalarSupport.V_support_equiv._proof_2
#print axioms ExactFourierCircuits.ScalarSupport.V_support_equiv._proof_3
#print axioms ExactFourierCircuits.ScalarSupport.V_support_equiv._proof_4
#print axioms ExactFourierCircuits.ScalarSupport.incidenceEquiv
#print axioms ExactFourierCircuits.ScalarSupport.incidenceEquiv._proof_1
#print axioms ExactFourierCircuits.ScalarSupport.incidenceEquiv._proof_2
#print axioms ExactFourierCircuits.ScalarSupport.incidenceEquiv._proof_3
#print axioms ExactFourierCircuits.ScalarSupport.incidenceEquiv._proof_4
#print axioms ExactFourierCircuits.ScalarSupport.incidenceEquiv._proof_5
#print axioms ExactFourierCircuits.ScalarSupport.incidenceEquiv._proof_6
#print axioms ExactFourierCircuits.ScalarSupport.incidenceEquiv._proof_7
#print axioms ExactFourierCircuits.ScalarSupport.incidenceEquiv.match_1
#print axioms ExactFourierCircuits.ScalarSupport.incidenceEquiv.match_3
#print axioms ExactFourierCircuits.ScalarSupport.invocation_support_count
#print axioms ExactFourierCircuits.ScalarSupport.neighbor_coefficient_ne_zero

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.ScalarSupport.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

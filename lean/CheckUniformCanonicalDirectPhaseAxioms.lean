import UniformCanonicalDirectPhase
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformCanonicalDirectPhase.direct_piece_phase_tick
#print axioms ExactFourierCircuits.UniformCanonicalDirectPhase.leaf_phase_tick
#print axioms ExactFourierCircuits.UniformCanonicalDirectPhase.operationPhase
#print axioms ExactFourierCircuits.UniformCanonicalDirectPhase.operationPhase._proof_1
#print axioms ExactFourierCircuits.UniformCanonicalDirectPhase.operationPhase.congr_simp
#print axioms ExactFourierCircuits.UniformCanonicalDirectPhase.operationPhase.eq_1
#print axioms ExactFourierCircuits.UniformCanonicalDirectPhase.operationPhase.eq_2
#print axioms ExactFourierCircuits.UniformCanonicalDirectPhase.operationPhase.match_1
#print axioms ExactFourierCircuits.UniformCanonicalDirectPhase.operationPhase_tick
#print axioms ExactFourierCircuits.UniformCanonicalDirectPhase.pairPhase
#print axioms ExactFourierCircuits.UniformCanonicalDirectPhase.pairPhase.eq_1
#print axioms ExactFourierCircuits.UniformCanonicalDirectPhase.pairPhase.eq_2
#print axioms ExactFourierCircuits.UniformCanonicalDirectPhase.pairPhase.match_1
#print axioms ExactFourierCircuits.UniformCanonicalDirectPhase.pairPhase_matrix
#print axioms ExactFourierCircuits.UniformCanonicalDirectPhase.scalePhase
#print axioms ExactFourierCircuits.UniformCanonicalDirectPhase.scalePhase._proof_1
#print axioms ExactFourierCircuits.UniformCanonicalDirectPhase.shearPhase
#print axioms ExactFourierCircuits.UniformCanonicalDirectPhase.shearPhase._proof_1
#print axioms ExactFourierCircuits.UniformCanonicalDirectPhase.shearPhase._proof_2
#print axioms ExactFourierCircuits.UniformCanonicalDirectPhase.shearPhase.eq_1

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformCanonicalDirectPhase.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

import UniformFinalRoleCaller
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalRoleCaller.LocalStages.bound
#print axioms ExactFourierCircuits.UniformFinalRoleCaller.data
#print axioms ExactFourierCircuits.UniformFinalRoleCaller.data._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalRoleCaller.data._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalRoleCaller.data._proof_1_3
#print axioms ExactFourierCircuits.UniformFinalRoleCaller.data._proof_1_4
#print axioms ExactFourierCircuits.UniformFinalRoleCaller.data._proof_1_5
#print axioms ExactFourierCircuits.UniformFinalRoleCaller.frame_before_pc
#print axioms ExactFourierCircuits.UniformFinalRoleCaller.frame_pc
#print axioms ExactFourierCircuits.UniformFinalRoleCaller.frame_trans
#print axioms ExactFourierCircuits.UniformFinalRoleCaller.kernel
#print axioms ExactFourierCircuits.UniformFinalRoleCaller.source_address
#print axioms ExactFourierCircuits.UniformFinalRoleCaller.volume_positive
#print axioms ExactFourierCircuits.UniformFinalRoleCaller.volume_positive._proof_1_1

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalRoleCaller.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

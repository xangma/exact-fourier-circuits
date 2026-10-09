import UniformFinalRoleAlpha
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalRoleAlpha.cells
#print axioms ExactFourierCircuits.UniformFinalRoleAlpha.execution
#print axioms ExactFourierCircuits.UniformFinalRoleAlpha.execution._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalRoleAlpha.execution._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalRoleAlpha.execution._proof_1_3
#print axioms ExactFourierCircuits.UniformFinalRoleAlpha.execution._proof_1_4
#print axioms ExactFourierCircuits.UniformFinalRoleAlpha.execution._proof_1_5
#print axioms ExactFourierCircuits.UniformFinalRoleAlpha.frame
#print axioms ExactFourierCircuits.UniformFinalRoleAlpha.frame._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalRoleAlpha.frame._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalRoleAlpha.frame._proof_1_3
#print axioms ExactFourierCircuits.UniformFinalRoleAlpha.generic_cells
#print axioms ExactFourierCircuits.UniformFinalRoleAlpha.generic_cells._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalRoleAlpha.generic_cells._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalRoleAlpha.numeric_zero
#print axioms ExactFourierCircuits.UniformFinalRoleAlpha.physical
#print axioms ExactFourierCircuits.UniformFinalRoleAlpha.standard

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalRoleAlpha.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

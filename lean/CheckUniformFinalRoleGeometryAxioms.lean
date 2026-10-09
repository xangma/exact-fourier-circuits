import UniformFinalRoleGeometry
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalRoleGeometry.geometry
#print axioms ExactFourierCircuits.UniformFinalRoleGeometry.geometry._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalRoleGeometry.geometry._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalRoleGeometry.header_low
#print axioms ExactFourierCircuits.UniformFinalRoleGeometry.header_low._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalRoleGeometry.header_low._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalRoleGeometry.header_low._proof_1_3
#print axioms ExactFourierCircuits.UniformFinalRoleGeometry.roles_two

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalRoleGeometry.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

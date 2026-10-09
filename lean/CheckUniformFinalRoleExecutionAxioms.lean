import UniformFinalRoleExecution
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.casesOn
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.mk
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.mk._flat_ctor
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.natHeap
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.natReg
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.outputs
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.rec
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.recOn
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.roots
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.scalar
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.Frame.scalarReg
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.args_pc
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.args_transport
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.args_transport._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.args_transport._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.args_transport._proof_1_3
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.args_transport._proof_1_4
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.args_transport._proof_1_5
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.args_transport._proof_1_6
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.args_transport._proof_1_7
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.args_transport._proof_1_8
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.compose_frame
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.entry_cells
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.execution
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.execution._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.execution._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.execution._proof_1_3
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.execution._proof_1_4
#print axioms ExactFourierCircuits.UniformFinalRoleExecution.execution._proof_1_5

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalRoleExecution.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

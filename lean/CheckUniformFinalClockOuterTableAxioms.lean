import UniformFinalClockOuterTable
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.header
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.header._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.header._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.header._proof_1_3
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.header._proof_1_4
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.header._proof_1_5
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.header._proof_1_6
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.table
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.table._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.table._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.tableArgs
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.tableArgs._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.tableArgs._proof_1_10
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.tableArgs._proof_1_11
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.tableArgs._proof_1_12
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.tableArgs._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.tableArgs._proof_1_3
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.tableArgs._proof_1_4
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.tableArgs._proof_1_5
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.tableArgs._proof_1_6
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.tableArgs._proof_1_7
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.tableArgs._proof_1_8
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.tableArgs._proof_1_9
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.tables
#print axioms ExactFourierCircuits.UniformFinalMovementCaller.Header.of_table
#print axioms ExactFourierCircuits.UniformFinalMovementCaller.Header.of_table._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalMovementCaller.Header.of_table._proof_1_4
#print axioms ExactFourierCircuits.UniformFinalMovementCaller.Tables.of_table
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.S.eq_1
#print axioms ExactFourierCircuits.UniformFinalMovementGeometry.T.eq_1
#print axioms ExactFourierCircuits.UniformFinalPhysicalTablePrefix.Result.withPC

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalClockOuterTable.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

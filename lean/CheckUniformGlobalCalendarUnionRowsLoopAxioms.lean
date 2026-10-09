import UniformGlobalCalendarUnionRowsLoop
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.Args
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.Args.casesOn
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.Args.count
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.Args.mk
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.Args.mk._flat_ctor
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.Args.output
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.Args.pairs
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.Args.rec
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.Args.recOn
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.Args.used
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.boot.eq_1
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.boot_header
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.execution
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.execution._proof_1_1
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.execution._proof_1_3
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.execution._proof_1_4
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.execution._proof_1_5
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.execution._proof_1_7
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.execution._proof_1_8
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.finish.eq_1
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.finish_header
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.loop
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.loop._proof_1_1
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.loop._proof_1_2
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.loop._proof_1_3
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.loop._proof_1_4
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.loop._proof_1_5
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.loop._proof_1_6
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.loop._proof_1_7
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.writeRows.eq_1
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.writeRows.eq_2
#print axioms ExactFourierCircuits.UniformGlobalCalendarUnionRows.writeRows.eq_def

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformGlobalCalendarUnionRowsLoop.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

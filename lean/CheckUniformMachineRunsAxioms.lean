import UniformMachineRuns
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformMachine.BoundedRuns
#print axioms ExactFourierCircuits.UniformMachine.BoundedRuns.below
#print axioms ExactFourierCircuits.UniformMachine.BoundedRuns.below.casesOn
#print axioms ExactFourierCircuits.UniformMachine.BoundedRuns.below.next
#print axioms ExactFourierCircuits.UniformMachine.BoundedRuns.below.rec
#print axioms ExactFourierCircuits.UniformMachine.BoundedRuns.below.refl
#print axioms ExactFourierCircuits.UniformMachine.BoundedRuns.brecOn
#print axioms ExactFourierCircuits.UniformMachine.BoundedRuns.casesOn
#print axioms ExactFourierCircuits.UniformMachine.BoundedRuns.executes
#print axioms ExactFourierCircuits.UniformMachine.BoundedRuns.final_bound
#print axioms ExactFourierCircuits.UniformMachine.BoundedRuns.initial_bound
#print axioms ExactFourierCircuits.UniformMachine.BoundedRuns.next
#print axioms ExactFourierCircuits.UniformMachine.BoundedRuns.rec
#print axioms ExactFourierCircuits.UniformMachine.BoundedRuns.recOn
#print axioms ExactFourierCircuits.UniformMachine.BoundedRuns.refl
#print axioms ExactFourierCircuits.UniformMachine.BoundedRuns.runs
#print axioms ExactFourierCircuits.UniformMachine.BoundedRuns.trans
#print axioms ExactFourierCircuits.UniformMachine.Executes.bounded_of_invariant
#print axioms ExactFourierCircuits.UniformMachine.Runs
#print axioms ExactFourierCircuits.UniformMachine.Runs.below
#print axioms ExactFourierCircuits.UniformMachine.Runs.below.casesOn
#print axioms ExactFourierCircuits.UniformMachine.Runs.below.next
#print axioms ExactFourierCircuits.UniformMachine.Runs.below.rec
#print axioms ExactFourierCircuits.UniformMachine.Runs.below.refl
#print axioms ExactFourierCircuits.UniformMachine.Runs.bounded_of_invariant
#print axioms ExactFourierCircuits.UniformMachine.Runs.brecOn
#print axioms ExactFourierCircuits.UniformMachine.Runs.casesOn
#print axioms ExactFourierCircuits.UniformMachine.Runs.executes
#print axioms ExactFourierCircuits.UniformMachine.Runs.next
#print axioms ExactFourierCircuits.UniformMachine.Runs.rec
#print axioms ExactFourierCircuits.UniformMachine.Runs.recOn
#print axioms ExactFourierCircuits.UniformMachine.Runs.refl
#print axioms ExactFourierCircuits.UniformMachine.Runs.trans
#print axioms ExactFourierCircuits.UniformMachine.changePC_bound
#print axioms ExactFourierCircuits.UniformMachine.emit_bound
#print axioms ExactFourierCircuits.UniformMachine.field_step_write
#print axioms ExactFourierCircuits.UniformMachine.next.eq_1
#print axioms ExactFourierCircuits.UniformMachine.step.eq_1
#print axioms ExactFourierCircuits.UniformMachine.writeNat.eq_1
#print axioms ExactFourierCircuits.UniformMachine.writeNat_bound
#print axioms ExactFourierCircuits.UniformMachine.writeScalar_bound

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformMachineRuns.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

import UniformRecursiveActualRuntime
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformRecursiveActualRuntime.actual_base
#print axioms ExactFourierCircuits.UniformRecursiveActualRuntime.actual_critical_bound
#print axioms ExactFourierCircuits.UniformRecursiveActualRuntime.actual_isBigO
#print axioms ExactFourierCircuits.UniformRecursiveActualRuntime.actual_node_call_charge
#print axioms ExactFourierCircuits.UniformRecursiveActualRuntime.actual_recurrence
#print axioms ExactFourierCircuits.UniformRecursiveActualRuntime.actual_static_node_charge
#print axioms ExactFourierCircuits.UniformRecursiveActualRuntime.criticalConstant
#print axioms ExactFourierCircuits.UniformRecursiveActualRuntime.recurrenceUnit
#print axioms ExactFourierCircuits.UniformRecursiveActualRuntime.stepUnit
#print axioms ExactFourierCircuits.UniformRecursiveActualRuntime.stepUnit_lower
#print axioms ExactFourierCircuits.UniformRecursiveActualRuntime.threshold_lower

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformRecursiveActualRuntime.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

import UniformKernelClockFrame
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformGlobalRoleScatterMachine.programFor.eq_1
#print axioms ExactFourierCircuits.UniformKernelClockFrame.actual_bounded_frame
#print axioms ExactFourierCircuits.UniformKernelClockFrame.actual_bounded_runs_frame
#print axioms ExactFourierCircuits.UniformKernelClockFrame.actual_startup_bounded_frame
#print axioms ExactFourierCircuits.UniformKernelClockFrame.actual_startup_bounded_runs_frame
#print axioms ExactFourierCircuits.UniformKernelClockFrame.assembly_safe
#print axioms ExactFourierCircuits.UniformKernelClockFrame.bounded_frame
#print axioms ExactFourierCircuits.UniformKernelClockFrame.initialized_safe
#print axioms ExactFourierCircuits.UniformKernelClockFrame.inverse_safe
#print axioms ExactFourierCircuits.UniformKernelClockFrame.kernel_safe
#print axioms ExactFourierCircuits.UniformKernelClockFrame.loop_safe
#print axioms ExactFourierCircuits.UniformKernelClockFrame.movement_safe
#print axioms ExactFourierCircuits.UniformKernelClockFrame.relocate_safe_eq

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformKernelClockFrame.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

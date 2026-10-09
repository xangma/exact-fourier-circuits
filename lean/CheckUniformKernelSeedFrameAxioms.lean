import UniformKernelSeedFrame
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformKernelSeedFrame.actual_bounded_frame
#print axioms ExactFourierCircuits.UniformKernelSeedFrame.actual_bounded_runs_frame
#print axioms ExactFourierCircuits.UniformKernelSeedFrame.assembly_safe
#print axioms ExactFourierCircuits.UniformKernelSeedFrame.bounded_frame
#print axioms ExactFourierCircuits.UniformKernelSeedFrame.initialized_safe
#print axioms ExactFourierCircuits.UniformKernelSeedFrame.inverse_safe
#print axioms ExactFourierCircuits.UniformKernelSeedFrame.kernel_safe
#print axioms ExactFourierCircuits.UniformKernelSeedFrame.loop_safe
#print axioms ExactFourierCircuits.UniformKernelSeedFrame.movement_safe
#print axioms ExactFourierCircuits.UniformKernelSeedFrame.relocate_safe_eq

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformKernelSeedFrame.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

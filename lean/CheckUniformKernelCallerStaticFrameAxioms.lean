import UniformKernelCallerStaticFrame
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformKernelCallerStaticFrame.assembly_safe
#print axioms ExactFourierCircuits.UniformKernelCallerStaticFrame.bounded_frame
#print axioms ExactFourierCircuits.UniformKernelCallerStaticFrame.initialized_safe
#print axioms ExactFourierCircuits.UniformKernelCallerStaticFrame.inverse_safe
#print axioms ExactFourierCircuits.UniformKernelCallerStaticFrame.kernel_safe
#print axioms ExactFourierCircuits.UniformKernelCallerStaticFrame.loop_safe
#print axioms ExactFourierCircuits.UniformKernelCallerStaticFrame.movement_safe
#print axioms ExactFourierCircuits.UniformKernelCallerStaticFrame.relocate_safe_eq

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformKernelCallerStaticFrame.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

import UniformFinalKernelClockSave
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.Result
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.Result.beforePC
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.Result.cache
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.Result.casesOn
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.Result.copied
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.Result.copyFrame
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.Result.frame
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.Result.kernelCells
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.Result.mk
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.Result.mk._flat_ctor
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.Result.movement
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.Result.numeric
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.Result.pc
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.Result.rec
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.Result.recOn
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.Result.runtime
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.Result.saved
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.Result.table
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.Result.transform
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.budget
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.execution
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.execution_local
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.kernelBase
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.kernelBase.eq_1
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.savedBase
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.stages_beforePC
#print axioms ExactFourierCircuits.UniformFinalKernelClockSave.volume

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalKernelClockSave.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

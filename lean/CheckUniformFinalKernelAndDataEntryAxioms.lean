import UniformFinalKernelAndDataEntry
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalKernelAndDataEntry.A
#print axioms ExactFourierCircuits.UniformFinalKernelAndDataEntry.B
#print axioms ExactFourierCircuits.UniformFinalKernelAndDataEntry.DK
#print axioms ExactFourierCircuits.UniformFinalKernelAndDataEntry.Q
#print axioms ExactFourierCircuits.UniformFinalKernelAndDataEntry.Result
#print axioms ExactFourierCircuits.UniformFinalKernelAndDataEntry.Result.casesOn
#print axioms ExactFourierCircuits.UniformFinalKernelAndDataEntry.Result.dataInput
#print axioms ExactFourierCircuits.UniformFinalKernelAndDataEntry.Result.entry
#print axioms ExactFourierCircuits.UniformFinalKernelAndDataEntry.Result.kernelInput
#print axioms ExactFourierCircuits.UniformFinalKernelAndDataEntry.Result.kernelRun
#print axioms ExactFourierCircuits.UniformFinalKernelAndDataEntry.Result.kernelSaved
#print axioms ExactFourierCircuits.UniformFinalKernelAndDataEntry.Result.kernelTags
#print axioms ExactFourierCircuits.UniformFinalKernelAndDataEntry.Result.mk
#print axioms ExactFourierCircuits.UniformFinalKernelAndDataEntry.Result.mk._flat_ctor
#print axioms ExactFourierCircuits.UniformFinalKernelAndDataEntry.Result.rec
#print axioms ExactFourierCircuits.UniformFinalKernelAndDataEntry.Result.recOn
#print axioms ExactFourierCircuits.UniformFinalKernelAndDataEntry.Result.saved
#print axioms ExactFourierCircuits.UniformFinalKernelAndDataEntry.Result.table
#print axioms ExactFourierCircuits.UniformFinalKernelAndDataEntry.V
#print axioms ExactFourierCircuits.UniformFinalKernelAndDataEntry.W
#print axioms ExactFourierCircuits.UniformFinalKernelAndDataEntry.cost
#print axioms ExactFourierCircuits.UniformFinalKernelAndDataEntry.execution
#print axioms ExactFourierCircuits.UniformFinalKernelAndDataEntry.stages

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalKernelAndDataEntry.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

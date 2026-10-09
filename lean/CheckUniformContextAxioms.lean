import UniformContext
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformContext.ContextFree
#print axioms ExactFourierCircuits.UniformContext.ContextFree.eq_1
#print axioms ExactFourierCircuits.UniformContext.bounded_execution
#print axioms ExactFourierCircuits.UniformContext.bounded_runs
#print axioms ExactFourierCircuits.UniformContext.execution
#print axioms ExactFourierCircuits.UniformContext.fft_heap_in_context
#print axioms ExactFourierCircuits.UniformContext.fft_in_context
#print axioms ExactFourierCircuits.UniformContext.instructionFree
#print axioms ExactFourierCircuits.UniformContext.instructionFree._sparseCasesOn_1
#print axioms ExactFourierCircuits.UniformContext.instructionFree._sparseCasesOn_1.else_eq
#print axioms ExactFourierCircuits.UniformContext.instructionFree.eq_1
#print axioms ExactFourierCircuits.UniformContext.instructionFree.eq_2
#print axioms ExactFourierCircuits.UniformContext.instructionFree.eq_3
#print axioms ExactFourierCircuits.UniformContext.instructionFree.eq_4
#print axioms ExactFourierCircuits.UniformContext.instructionFree.match_1
#print axioms ExactFourierCircuits.UniformContext.preparation_contextFree
#print axioms ExactFourierCircuits.UniformContext.runs
#print axioms ExactFourierCircuits.UniformContext.step_same

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformContext.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

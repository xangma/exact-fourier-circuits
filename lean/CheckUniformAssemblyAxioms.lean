import UniformAssembly
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformAssembly.BoundedExecution.placed
#print axioms ExactFourierCircuits.UniformAssembly.BoundedExecution.placed._proof_1_1
#print axioms ExactFourierCircuits.UniformAssembly.BoundedRuns.placed
#print axioms ExactFourierCircuits.UniformAssembly.CodeAt
#print axioms ExactFourierCircuits.UniformAssembly.Executes.placed
#print axioms ExactFourierCircuits.UniformAssembly.Runs.placed
#print axioms ExactFourierCircuits.UniformAssembly.embed
#print axioms ExactFourierCircuits.UniformAssembly.embed.eq_1
#print axioms ExactFourierCircuits.UniformAssembly.embed_code
#print axioms ExactFourierCircuits.UniformAssembly.embed_length
#print axioms ExactFourierCircuits.UniformAssembly.halted_pc
#print axioms ExactFourierCircuits.UniformAssembly.halted_placed
#print axioms ExactFourierCircuits.UniformAssembly.placed
#print axioms ExactFourierCircuits.UniformAssembly.placed.eq_1
#print axioms ExactFourierCircuits.UniformAssembly.placedResult
#print axioms ExactFourierCircuits.UniformAssembly.placedResult.eq_1
#print axioms ExactFourierCircuits.UniformAssembly.placedResult.eq_2
#print axioms ExactFourierCircuits.UniformAssembly.placedResult.eq_3
#print axioms ExactFourierCircuits.UniformAssembly.placedResult.match_1
#print axioms ExactFourierCircuits.UniformAssembly.placed_bound
#print axioms ExactFourierCircuits.UniformAssembly.placed_bound._proof_1_1
#print axioms ExactFourierCircuits.UniformAssembly.relocate
#print axioms ExactFourierCircuits.UniformAssembly.relocate._sparseCasesOn_1
#print axioms ExactFourierCircuits.UniformAssembly.relocate._sparseCasesOn_1.else_eq
#print axioms ExactFourierCircuits.UniformAssembly.relocate.eq_1
#print axioms ExactFourierCircuits.UniformAssembly.relocate.eq_2
#print axioms ExactFourierCircuits.UniformAssembly.relocate.eq_3
#print axioms ExactFourierCircuits.UniformAssembly.relocate.eq_4
#print axioms ExactFourierCircuits.UniformAssembly.relocate.match_1
#print axioms ExactFourierCircuits.UniformAssembly.running_pc
#print axioms ExactFourierCircuits.UniformAssembly.running_placed
#print axioms ExactFourierCircuits.UniformAssembly.step_placed
#print axioms ExactFourierCircuits.UniformAssembly.wordBound_mono
#print axioms ExactFourierCircuits.UniformMachine.writeScalar.eq_1

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformAssembly.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

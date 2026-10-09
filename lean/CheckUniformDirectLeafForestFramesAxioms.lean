import UniformDirectLeafForestFrames
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformDirectLeafForestFrames.execution_nat
#print axioms ExactFourierCircuits.UniformDirectLeafForestFrames.free
#print axioms ExactFourierCircuits.UniformDirectLeafForestFrames.free._sparseCasesOn_1
#print axioms ExactFourierCircuits.UniformDirectLeafForestFrames.free._sparseCasesOn_1.else_eq
#print axioms ExactFourierCircuits.UniformDirectLeafForestFrames.free.eq_1
#print axioms ExactFourierCircuits.UniformDirectLeafForestFrames.free.eq_2
#print axioms ExactFourierCircuits.UniformDirectLeafForestFrames.free.eq_3
#print axioms ExactFourierCircuits.UniformDirectLeafForestFrames.free.eq_4
#print axioms ExactFourierCircuits.UniformDirectLeafForestFrames.free.eq_5
#print axioms ExactFourierCircuits.UniformDirectLeafForestFrames.free.match_1
#print axioms ExactFourierCircuits.UniformDirectLeafForestFrames.free_leaf
#print axioms ExactFourierCircuits.UniformDirectLeafForestFrames.free_leaf._proof_1_7
#print axioms ExactFourierCircuits.UniformDirectLeafForestFrames.free_program
#print axioms ExactFourierCircuits.UniformDirectLeafForestFrames.free_relocate
#print axioms ExactFourierCircuits.UniformDirectLeafForestFrames.keeps
#print axioms ExactFourierCircuits.UniformDirectLeafForestFrames.keeps._proof_1_7

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformDirectLeafForestFrames.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

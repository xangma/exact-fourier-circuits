import UniformDirectLeafForestBankFrame
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformDirectLeafForestBankFrame.execution_bank
#print axioms ExactFourierCircuits.UniformDirectLeafForestBankFrame.free
#print axioms ExactFourierCircuits.UniformDirectLeafForestBankFrame.free._sparseCasesOn_1
#print axioms ExactFourierCircuits.UniformDirectLeafForestBankFrame.free._sparseCasesOn_1.else_eq
#print axioms ExactFourierCircuits.UniformDirectLeafForestBankFrame.free.eq_1
#print axioms ExactFourierCircuits.UniformDirectLeafForestBankFrame.free.eq_2
#print axioms ExactFourierCircuits.UniformDirectLeafForestBankFrame.free.eq_3
#print axioms ExactFourierCircuits.UniformDirectLeafForestBankFrame.free.eq_4
#print axioms ExactFourierCircuits.UniformDirectLeafForestBankFrame.free.eq_5
#print axioms ExactFourierCircuits.UniformDirectLeafForestBankFrame.free.match_1
#print axioms ExactFourierCircuits.UniformDirectLeafForestBankFrame.free_leaf
#print axioms ExactFourierCircuits.UniformDirectLeafForestBankFrame.free_leaf._proof_1_7
#print axioms ExactFourierCircuits.UniformDirectLeafForestBankFrame.free_program
#print axioms ExactFourierCircuits.UniformDirectLeafForestBankFrame.free_relocate
#print axioms ExactFourierCircuits.UniformDirectLeafForestBankFrame.keeps
#print axioms ExactFourierCircuits.UniformDirectLeafForestBankFrame.keeps._proof_1_7

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformDirectLeafForestBankFrame.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

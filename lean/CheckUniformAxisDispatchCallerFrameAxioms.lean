import UniformAxisDispatchCallerFrame
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformAxisDispatchCallerFrame.Kept
#print axioms ExactFourierCircuits.UniformAxisDispatchCallerFrame.Safe
#print axioms ExactFourierCircuits.UniformAxisDispatchCallerFrame.Safe.eq_1
#print axioms ExactFourierCircuits.UniformAxisDispatchCallerFrame.Safe.match_1
#print axioms ExactFourierCircuits.UniformAxisDispatchCallerFrame.SafeProgram
#print axioms ExactFourierCircuits.UniformAxisDispatchCallerFrame.adapter
#print axioms ExactFourierCircuits.UniformAxisDispatchCallerFrame.adapter_safe
#print axioms ExactFourierCircuits.UniformAxisDispatchCallerFrame.adapter_safe._proof_1_1
#print axioms ExactFourierCircuits.UniformAxisDispatchCallerFrame.avoids
#print axioms ExactFourierCircuits.UniformAxisDispatchCallerFrame.avoids._proof_1_2
#print axioms ExactFourierCircuits.UniformAxisDispatchCallerFrame.checked
#print axioms ExactFourierCircuits.UniformAxisDispatchCallerFrame.dispatch
#print axioms ExactFourierCircuits.UniformAxisDispatchCallerFrame.dispatch_safe
#print axioms ExactFourierCircuits.UniformAxisDispatchCallerFrame.dispatch_safe._proof_1_1
#print axioms ExactFourierCircuits.UniformAxisDispatchCallerFrame.instDecidableSafe
#print axioms ExactFourierCircuits.UniformAxisDispatchCallerFrame.instDecidableSafe._proof_1
#print axioms ExactFourierCircuits.UniformAxisDispatchCallerFrame.instDecidableSafe._proof_2
#print axioms ExactFourierCircuits.UniformAxisDispatchCallerFrame.instDecidableSafe._proof_3

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformAxisDispatchCallerFrame.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

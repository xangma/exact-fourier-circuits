import UniformFinalAxisStartupFrame
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalAxisStartupFrame.Kept
#print axioms ExactFourierCircuits.UniformFinalAxisStartupFrame.Safe
#print axioms ExactFourierCircuits.UniformFinalAxisStartupFrame.Safe.eq_1
#print axioms ExactFourierCircuits.UniformFinalAxisStartupFrame.Safe.match_1
#print axioms ExactFourierCircuits.UniformFinalAxisStartupFrame.adapter
#print axioms ExactFourierCircuits.UniformFinalAxisStartupFrame.adapter_safe
#print axioms ExactFourierCircuits.UniformFinalAxisStartupFrame.adapter_safe._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalAxisStartupFrame.avoids
#print axioms ExactFourierCircuits.UniformFinalAxisStartupFrame.avoids._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalAxisStartupFrame.checked
#print axioms ExactFourierCircuits.UniformFinalAxisStartupFrame.dispatch
#print axioms ExactFourierCircuits.UniformFinalAxisStartupFrame.dispatch_safe
#print axioms ExactFourierCircuits.UniformFinalAxisStartupFrame.dispatch_safe._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalAxisStartupFrame.instDecidableSafe
#print axioms ExactFourierCircuits.UniformFinalAxisStartupFrame.instDecidableSafe._proof_1
#print axioms ExactFourierCircuits.UniformFinalAxisStartupFrame.instDecidableSafe._proof_2
#print axioms ExactFourierCircuits.UniformFinalAxisStartupFrame.instDecidableSafe._proof_3
#print axioms ExactFourierCircuits.UniformFinalAxisStartupFrame.prepare
#print axioms ExactFourierCircuits.UniformFinalAxisStartupFrame.prepare_safe
#print axioms ExactFourierCircuits.UniformFinalAxisStartupFrame.prepare_safe._proof_1_1

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalAxisStartupFrame.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

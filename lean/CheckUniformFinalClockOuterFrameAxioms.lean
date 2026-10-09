import UniformFinalClockOuterFrame
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.alpha
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.beforePC
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.cache
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.casesOn
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.inverse
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.low
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.mk
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.mk._flat_ctor
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.natReg
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.outputs
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.rec
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.recOn
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.refl
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.roots
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.runtime
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.runtime._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.runtime._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.runtime._proof_1_3
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.saved
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.trans
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.withPC
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.RequiredNat
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.RuntimeNat
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Spectrum

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalClockOuterFrame.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

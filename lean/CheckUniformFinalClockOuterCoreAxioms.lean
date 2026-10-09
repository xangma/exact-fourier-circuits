import UniformFinalClockOuterCore
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.cache_all
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.conjugate
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.core
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.core._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.core._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.core._proof_1_3
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.core._proof_1_4
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.core._proof_1_5
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.core._proof_1_6
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.data
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.inputs
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.original
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.original._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalClockOuterRetention.Frame.original._proof_1_2

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalClockOuterCore.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

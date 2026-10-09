import UniformFinalMovementFrame
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.beforePC
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.cache_all
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.cache_heaps
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.casesOn
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.copy
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.copy._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.copy._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.core
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.core._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.core._proof_1_10
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.core._proof_1_11
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.core._proof_1_12
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.core._proof_1_13
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.core._proof_1_14
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.core._proof_1_15
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.core._proof_1_16
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.core._proof_1_17
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.core._proof_1_18
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.core._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.core._proof_1_3
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.core._proof_1_4
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.core._proof_1_5
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.core._proof_1_6
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.core._proof_1_7
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.core._proof_1_8
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.core._proof_1_9
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.crt
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.crt._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.crt._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.crt._proof_1_3
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.crt._proof_1_4
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.high
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.low
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.mk
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.mk._flat_ctor
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.natHeap
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.outputs
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.pointwise
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.pointwise._proof_1_1
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.pointwise._proof_1_2
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.pointwise._proof_1_3
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.rec
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.recOn
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.roots
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.saved
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.scalar
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.trans
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Frame.withPC
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.Q
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.low_bound
#print axioms ExactFourierCircuits.UniformFinalMovementFrame.low_bound._proof_1_1

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalMovementFrame.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

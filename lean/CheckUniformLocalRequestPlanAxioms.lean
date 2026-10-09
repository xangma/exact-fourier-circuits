import UniformLocalRequestPlan
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Request
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Request._sizeOf_1
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Request._sizeOf_inst
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Request.casesOn
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Request.ctorIdx
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Request.mk
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Request.mk._flat_ctor
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Request.mk.inj
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Request.mk.injEq
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Request.mk.noConfusion
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Request.mk.sizeOf_spec
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Request.noConfusion
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Request.noConfusionType
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Request.rec
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Request.recOn
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Request.row
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Request.time
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Source
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Source.casesOn
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Source.mk
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Source.mk._flat_ctor
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Source.rec
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Source.recOn
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Source.rows
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Source.times
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.Source.transport
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.controller
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.controller.eq_1
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.controller_count
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.prefix_mono
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.prefix_mono._proof_1_1
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.prefix_mono._proof_1_2
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.prefix_mono._proof_1_3
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.prefix_mono._proof_1_4
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.prefix_step
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.prefix_zero
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.requestAt
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.requestAt.eq_1
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.requestAt_eq
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.slotCount
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.slotPrefix
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.slotPrefix._f
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.slotPrefix._sunfold
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.slotPrefix._unsafe_rec
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.slotPrefix.eq_1
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.slotPrefix.eq_2
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.slotPrefix.eq_3
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.slotPrefix.eq_def
#print axioms ExactFourierCircuits.UniformLocalRequestPlan.slotPrefix.match_1

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformLocalRequestPlan.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

import ProjectionIdentities
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.Projection.DirtyState
#print axioms ExactFourierCircuits.Projection.DirtyState._sizeOf_1
#print axioms ExactFourierCircuits.Projection.DirtyState._sizeOf_inst
#print axioms ExactFourierCircuits.Projection.DirtyState.auxiliaryA
#print axioms ExactFourierCircuits.Projection.DirtyState.auxiliaryC
#print axioms ExactFourierCircuits.Projection.DirtyState.casesOn
#print axioms ExactFourierCircuits.Projection.DirtyState.ctorIdx
#print axioms ExactFourierCircuits.Projection.DirtyState.ext
#print axioms ExactFourierCircuits.Projection.DirtyState.ext.match_1
#print axioms ExactFourierCircuits.Projection.DirtyState.ext_iff
#print axioms ExactFourierCircuits.Projection.DirtyState.mk
#print axioms ExactFourierCircuits.Projection.DirtyState.mk._flat_ctor
#print axioms ExactFourierCircuits.Projection.DirtyState.mk.inj
#print axioms ExactFourierCircuits.Projection.DirtyState.mk.injEq
#print axioms ExactFourierCircuits.Projection.DirtyState.mk.noConfusion
#print axioms ExactFourierCircuits.Projection.DirtyState.mk.sizeOf_spec
#print axioms ExactFourierCircuits.Projection.DirtyState.noConfusion
#print axioms ExactFourierCircuits.Projection.DirtyState.noConfusionType
#print axioms ExactFourierCircuits.Projection.DirtyState.rec
#print axioms ExactFourierCircuits.Projection.DirtyState.recOn
#print axioms ExactFourierCircuits.Projection.DirtyState.x
#print axioms ExactFourierCircuits.Projection.DirtyState.y
#print axioms ExactFourierCircuits.Projection.directionalC
#print axioms ExactFourierCircuits.Projection.directionalC.eq_1
#print axioms ExactFourierCircuits.Projection.directionalC_inverse
#print axioms ExactFourierCircuits.Projection.eightRows
#print axioms ExactFourierCircuits.Projection.eightRows.eq_1
#print axioms ExactFourierCircuits.Projection.eightRows_identity
#print axioms ExactFourierCircuits.Projection.eightRows_identity._abel_1_1
#print axioms ExactFourierCircuits.Projection.frame_telescoping
#print axioms ExactFourierCircuits.Projection.frame_telescoping_apply
#print axioms ExactFourierCircuits.Projection.framedGate
#print axioms ExactFourierCircuits.Projection.framedGate.eq_1
#print axioms ExactFourierCircuits.Projection.intertwines_comp
#print axioms ExactFourierCircuits.Projection.intertwines_runWord
#print axioms ExactFourierCircuits.Projection.inverseDirectionalC
#print axioms ExactFourierCircuits.Projection.inverseDirectionalC.eq_1
#print axioms ExactFourierCircuits.Projection.pointwise
#print axioms ExactFourierCircuits.Projection.pullback
#print axioms ExactFourierCircuits.Projection.pullback.eq_1
#print axioms ExactFourierCircuits.Projection.pullback_directionalC
#print axioms ExactFourierCircuits.Projection.pullback_injective
#print axioms ExactFourierCircuits.Projection.pullback_inverseDirectionalC
#print axioms ExactFourierCircuits.Projection.pullback_pointwise
#print axioms ExactFourierCircuits.Projection.pullback_translate
#print axioms ExactFourierCircuits.Projection.rolePullback
#print axioms ExactFourierCircuits.Projection.runStages
#print axioms ExactFourierCircuits.Projection.runStages._f
#print axioms ExactFourierCircuits.Projection.runStages._sunfold
#print axioms ExactFourierCircuits.Projection.runStages._unsafe_rec
#print axioms ExactFourierCircuits.Projection.runStages.eq_1
#print axioms ExactFourierCircuits.Projection.runStages.eq_2
#print axioms ExactFourierCircuits.Projection.runStages.eq_def
#print axioms ExactFourierCircuits.Projection.runStages.match_1
#print axioms ExactFourierCircuits.Projection.runWord
#print axioms ExactFourierCircuits.Projection.runWord._f
#print axioms ExactFourierCircuits.Projection.runWord._sunfold
#print axioms ExactFourierCircuits.Projection.runWord._unsafe_rec
#print axioms ExactFourierCircuits.Projection.runWord.eq_1
#print axioms ExactFourierCircuits.Projection.runWord.eq_2
#print axioms ExactFourierCircuits.Projection.runWord.eq_def
#print axioms ExactFourierCircuits.Projection.runWord.match_1
#print axioms ExactFourierCircuits.Projection.scalar_exchange
#print axioms ExactFourierCircuits.Projection.swapBanks
#print axioms ExactFourierCircuits.Projection.swapBanks.eq_1
#print axioms ExactFourierCircuits.Projection.translate
#print axioms ExactFourierCircuits.Projection.translate.eq_1

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.ProjectionIdentities.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

import UniformSmallAxesTensorAction
import Lean
set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.axisCoordinates_update
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.axisTransform_action
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.execution_tensor
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.full_action
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.full_action._proof_1_2
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.largeStage
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.largeStage.eq_1
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.lifted
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.lifted.eq_1
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.oneValue_action
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.partialLocal
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.partialLocal.eq_1
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.partial_step
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.partial_step._proof_1_2
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.partial_step._proof_1_3
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.prefix_action
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.prefix_action._proof_1_2
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.prefix_action._proof_1_6
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.runtime_linear
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.runtime_linear._proof_1_1
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.runtime_linear._proof_1_2
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.split_complete
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.stage
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.stage.eq_1
#print axioms ExactFourierCircuits.UniformSmallAxesTensorAction.tensor_axis_action

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformSmallAxesTensorAction.".isPrefixOf name.toString then
   let axioms ← collectAxioms name
   for ax in axioms do
    unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
     throwError m!"Nonstandard axiom {ax} in {name}"
   logInfo m!"{name} depends on axioms: {axioms.toList}"

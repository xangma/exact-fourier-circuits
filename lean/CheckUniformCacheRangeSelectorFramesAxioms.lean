import UniformCacheRangeSelectorFrames
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformCacheRangeSelector.selectorFootprint
#print axioms ExactFourierCircuits.UniformCacheRangeSelector.selectorInstruction
#print axioms ExactFourierCircuits.UniformCacheRangeSelector.selectorInstruction._sparseCasesOn_1
#print axioms ExactFourierCircuits.UniformCacheRangeSelector.selectorInstruction._sparseCasesOn_1.else_eq
#print axioms ExactFourierCircuits.UniformCacheRangeSelector.selectorInstruction.eq_1
#print axioms ExactFourierCircuits.UniformCacheRangeSelector.selectorInstruction.eq_2
#print axioms ExactFourierCircuits.UniformCacheRangeSelector.selectorInstruction.eq_3
#print axioms ExactFourierCircuits.UniformCacheRangeSelector.selectorInstruction.eq_4
#print axioms ExactFourierCircuits.UniformCacheRangeSelector.selectorInstruction.eq_5
#print axioms ExactFourierCircuits.UniformCacheRangeSelector.selectorInstruction.match_1
#print axioms ExactFourierCircuits.UniformCacheRangeSelector.selector_control
#print axioms ExactFourierCircuits.UniformCacheRangeSelector.selector_control._proof_1_1
#print axioms ExactFourierCircuits.UniformCacheRangeSelector.selector_control._proof_1_2
#print axioms ExactFourierCircuits.UniformCacheRangeSelector.selector_control._proof_1_3
#print axioms ExactFourierCircuits.UniformCacheRangeSelector.selector_control._proof_1_4
#print axioms ExactFourierCircuits.UniformCacheRangeSelector.selector_control._proof_1_5
#print axioms ExactFourierCircuits.UniformCacheRangeSelector.selector_control._proof_1_6
#print axioms ExactFourierCircuits.UniformCacheRangeSelector.selector_control._proof_1_7
#print axioms ExactFourierCircuits.UniformCacheRangeSelector.selector_keeps
#print axioms ExactFourierCircuits.UniformCacheRangeSelector.selector_keeps._proof_1_7

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformCacheRangeSelectorFrames.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

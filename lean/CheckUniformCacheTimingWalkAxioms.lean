import UniformCacheTimingWalk
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformCacheTimingWalk.numbered
#print axioms ExactFourierCircuits.UniformCacheTimingWalk.numbered._f
#print axioms ExactFourierCircuits.UniformCacheTimingWalk.numbered._sunfold
#print axioms ExactFourierCircuits.UniformCacheTimingWalk.numbered._unsafe_rec
#print axioms ExactFourierCircuits.UniformCacheTimingWalk.numbered.eq_1
#print axioms ExactFourierCircuits.UniformCacheTimingWalk.numbered.eq_2
#print axioms ExactFourierCircuits.UniformCacheTimingWalk.numbered.eq_def
#print axioms ExactFourierCircuits.UniformCacheTimingWalk.numbered.match_1
#print axioms ExactFourierCircuits.UniformCacheTimingWalk.numbered_length
#print axioms ExactFourierCircuits.UniformCacheTimingWalk.numbered_length._proof_1_4
#print axioms ExactFourierCircuits.UniformCacheTimingWalk.root_walk_numbered
#print axioms ExactFourierCircuits.UniformCacheTimingWalk.root_walk_numbered._proof_1_1
#print axioms ExactFourierCircuits.UniformCacheTimingWalk.root_walk_numbered._proof_1_2
#print axioms ExactFourierCircuits.UniformCacheTimingWalk.root_walk_numbered._proof_1_3
#print axioms ExactFourierCircuits.UniformCacheTimingWalk.walk_add
#print axioms ExactFourierCircuits.UniformCacheTimingWalk.walk_add._proof_1_1
#print axioms ExactFourierCircuits.UniformCacheTimingWalk.walk_nil
#print axioms ExactFourierCircuits.UniformCacheTimingWalk.walk_numbered
#print axioms ExactFourierCircuits.UniformCacheTimingWalk.walk_numbered._proof_1_4
#print axioms ExactFourierCircuits.UniformCacheTimingWalk.walk_numbered._proof_1_5

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformCacheTimingWalk.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

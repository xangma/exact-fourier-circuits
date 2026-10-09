import UniformDirectLeafForestModel
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformDirectLeafForestModel.actual_capacity
#print axioms ExactFourierCircuits.UniformDirectLeafForestModel.actual_capacity._proof_1_1
#print axioms ExactFourierCircuits.UniformDirectLeafForestModel.before
#print axioms ExactFourierCircuits.UniformDirectLeafForestModel.before.eq_1
#print axioms ExactFourierCircuits.UniformDirectLeafForestModel.before_le
#print axioms ExactFourierCircuits.UniformDirectLeafForestModel.before_le._proof_1_1
#print axioms ExactFourierCircuits.UniformDirectLeafForestModel.before_length
#print axioms ExactFourierCircuits.UniformDirectLeafForestModel.before_next
#print axioms ExactFourierCircuits.UniformDirectLeafForestModel.before_zero
#print axioms ExactFourierCircuits.UniformDirectLeafForestModel.cachedBefore
#print axioms ExactFourierCircuits.UniformDirectLeafForestModel.cachedBefore.eq_1
#print axioms ExactFourierCircuits.UniformDirectLeafForestModel.cached_next
#print axioms ExactFourierCircuits.UniformDirectLeafForestModel.demand
#print axioms ExactFourierCircuits.UniformDirectLeafForestModel.demand.eq_1
#print axioms ExactFourierCircuits.UniformDirectLeafForestModel.demand_append
#print axioms ExactFourierCircuits.UniformDirectLeafForestModel.instDecidableLeaf
#print axioms ExactFourierCircuits.UniformDirectLeafForestModel.instDecidableLeaf._aux_1
#print axioms ExactFourierCircuits.UniformDirectLeafForestModel.leaf
#print axioms ExactFourierCircuits.UniformDirectLeafForestModel.numbered_demand
#print axioms ExactFourierCircuits.UniformDirectLeafForestModel.operations
#print axioms ExactFourierCircuits.UniformDirectLeafForestModel.root_demand
#print axioms ExactFourierCircuits.UniformJointCacheTime.leafOperations.eq_1
#print axioms ExactFourierCircuits.UniformJointCacheTime.leafOperations.eq_2
#print axioms ExactFourierCircuits.UniformJointCacheTime.leafOperations.eq_def

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformDirectLeafForestModel.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

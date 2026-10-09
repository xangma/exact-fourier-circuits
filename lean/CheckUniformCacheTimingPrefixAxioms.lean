import UniformCacheTimingPrefix
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformCacheTimingPrefix.amounts_eq
#print axioms ExactFourierCircuits.UniformCacheTimingPrefix.writePrefixes_inside
#print axioms ExactFourierCircuits.UniformCacheTimingPrefix.writePrefixes_inside._proof_1_4
#print axioms ExactFourierCircuits.UniformCacheTimingPrefix.writePrefixes_outside
#print axioms ExactFourierCircuits.UniformCacheTimingPrefix.writePrefixes_outside._proof_1_4
#print axioms ExactFourierCircuits.UniformCacheTimingPrefix.writePrefixes_outside._proof_1_5
#print axioms ExactFourierCircuits.UniformCacheTimingRows.writePrefixes.eq_1
#print axioms ExactFourierCircuits.UniformCacheTimingRows.writePrefixes.eq_2
#print axioms ExactFourierCircuits.UniformCacheTimingRows.writePrefixes.eq_def

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformCacheTimingPrefix.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

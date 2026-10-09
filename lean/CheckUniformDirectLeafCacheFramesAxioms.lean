import UniformDirectLeafCacheFrames
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformDirectLeafCacheFrames.execution_nat
#print axioms ExactFourierCircuits.UniformDirectLeafCacheFrames.execution_saved
#print axioms ExactFourierCircuits.UniformDirectLeafCacheFrames.free
#print axioms ExactFourierCircuits.UniformDirectLeafCacheFrames.free._sparseCasesOn_1
#print axioms ExactFourierCircuits.UniformDirectLeafCacheFrames.free._sparseCasesOn_1.else_eq
#print axioms ExactFourierCircuits.UniformDirectLeafCacheFrames.free.eq_1
#print axioms ExactFourierCircuits.UniformDirectLeafCacheFrames.free.eq_2
#print axioms ExactFourierCircuits.UniformDirectLeafCacheFrames.free.eq_3
#print axioms ExactFourierCircuits.UniformDirectLeafCacheFrames.free.eq_4
#print axioms ExactFourierCircuits.UniformDirectLeafCacheFrames.free.eq_5
#print axioms ExactFourierCircuits.UniformDirectLeafCacheFrames.free.match_1
#print axioms ExactFourierCircuits.UniformDirectLeafCacheFrames.free_program
#print axioms ExactFourierCircuits.UniformDirectLeafCacheFrames.keeps
#print axioms ExactFourierCircuits.UniformDirectLeafCacheFrames.keeps._proof_1_7
#print axioms ExactFourierCircuits.UniformDirectLeafCacheFrames.keeps_saved
#print axioms ExactFourierCircuits.UniformDirectLeafCacheFrames.keeps_saved._proof_1_7
#print axioms ExactFourierCircuits.UniformDirectLeafCacheFrames.savedFree
#print axioms ExactFourierCircuits.UniformDirectLeafCacheFrames.savedFree.eq_1
#print axioms ExactFourierCircuits.UniformDirectLeafCacheFrames.savedFree.eq_2
#print axioms ExactFourierCircuits.UniformDirectLeafCacheFrames.savedFree.eq_3
#print axioms ExactFourierCircuits.UniformDirectLeafCacheFrames.savedFree.eq_4
#print axioms ExactFourierCircuits.UniformDirectLeafCacheFrames.savedFree.eq_5
#print axioms ExactFourierCircuits.UniformDirectLeafCacheFrames.saved_free

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformDirectLeafCacheFrames.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

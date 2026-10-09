import UniformLocalCacheContextFrames
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformLocalCacheContextConductor.context_keeps
#print axioms ExactFourierCircuits.UniformLocalCacheContextConductor.context_keeps._proof_1_7
#print axioms ExactFourierCircuits.UniformLocalCacheContextConductor.context_protected
#print axioms ExactFourierCircuits.UniformLocalCacheContextConductor.execution_nat
#print axioms ExactFourierCircuits.UniformLocalCacheContextConductor.program_keeps
#print axioms ExactFourierCircuits.UniformLocalCacheContextConductor.protectedInstruction
#print axioms ExactFourierCircuits.UniformLocalCacheContextConductor.protectedInstruction._sparseCasesOn_1
#print axioms ExactFourierCircuits.UniformLocalCacheContextConductor.protectedInstruction._sparseCasesOn_1.else_eq
#print axioms ExactFourierCircuits.UniformLocalCacheContextConductor.protectedInstruction.eq_1
#print axioms ExactFourierCircuits.UniformLocalCacheContextConductor.protectedInstruction.eq_2
#print axioms ExactFourierCircuits.UniformLocalCacheContextConductor.protectedInstruction.eq_3
#print axioms ExactFourierCircuits.UniformLocalCacheContextConductor.protectedInstruction.eq_4
#print axioms ExactFourierCircuits.UniformLocalCacheContextConductor.protectedInstruction.eq_5
#print axioms ExactFourierCircuits.UniformLocalCacheContextConductor.protectedInstruction.match_1

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformLocalCacheContextFrames.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

import UniformLocalCacheTimingPlacement
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformLocalCacheTimingPlacement.TerminalCodeAt
#print axioms ExactFourierCircuits.UniformLocalCacheTimingPlacement.terminalRelocate
#print axioms ExactFourierCircuits.UniformLocalCacheTimingPlacement.terminalRelocate._sparseCasesOn_1
#print axioms ExactFourierCircuits.UniformLocalCacheTimingPlacement.terminalRelocate._sparseCasesOn_1.else_eq
#print axioms ExactFourierCircuits.UniformLocalCacheTimingPlacement.terminalRelocate.eq_1
#print axioms ExactFourierCircuits.UniformLocalCacheTimingPlacement.terminalRelocate.eq_2
#print axioms ExactFourierCircuits.UniformLocalCacheTimingPlacement.terminalRelocate.match_1
#print axioms ExactFourierCircuits.UniformLocalCacheTimingPlacement.terminalResult
#print axioms ExactFourierCircuits.UniformLocalCacheTimingPlacement.terminalResult.eq_1
#print axioms ExactFourierCircuits.UniformLocalCacheTimingPlacement.terminalResult.eq_2
#print axioms ExactFourierCircuits.UniformLocalCacheTimingPlacement.terminalResult.eq_3
#print axioms ExactFourierCircuits.UniformLocalCacheTimingPlacement.terminalResult.match_1
#print axioms ExactFourierCircuits.UniformLocalCacheTimingPlacement.terminal_execution
#print axioms ExactFourierCircuits.UniformLocalCacheTimingPlacement.terminal_execution._proof_1_1
#print axioms ExactFourierCircuits.UniformLocalCacheTimingPlacement.terminal_step

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformLocalCacheTimingPlacement.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

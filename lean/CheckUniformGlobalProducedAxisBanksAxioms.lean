import UniformGlobalProducedAxisBanks
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformGlobalDiagonalRowsMachine.Cell.eq_1
#print axioms ExactFourierCircuits.UniformGlobalDiagonalRowsMachine.Directory.eq_1
#print axioms ExactFourierCircuits.UniformGlobalDiagonalRowsMachine.Directory.eq_2
#print axioms ExactFourierCircuits.UniformGlobalDiagonalRowsMachine.Directory.eq_def
#print axioms ExactFourierCircuits.UniformGlobalProducedAxisBanks.banks_ofFn
#print axioms ExactFourierCircuits.UniformGlobalProducedAxisBanks.directory_ofFn
#print axioms ExactFourierCircuits.UniformGlobalProducedAxisBanks.directory_ofFn._proof_1_5
#print axioms ExactFourierCircuits.UniformGlobalProducedAxisBanks.permutations_ofFn
#print axioms ExactFourierCircuits.UniformGlobalProducedAxisBanks.permutations_ofFn._simp_1_1
#print axioms ExactFourierCircuits.UniformGlobalProducedAxisBanks.pools_ofFn
#print axioms ExactFourierCircuits.UniformGlobalProducedAxisBanks.rows_append
#print axioms ExactFourierCircuits.UniformGlobalProducedAxisBanks.rows_append._proof_1_4
#print axioms ExactFourierCircuits.UniformGlobalProducedAxisBanks.rows_ofFn
#print axioms ExactFourierCircuits.UniformGlobalProducedAxisBanks.rows_ofFn._proof_1_4
#print axioms ExactFourierCircuits.UniformGlobalProducedAxisBanks.rows_single_shift
#print axioms ExactFourierCircuits.UniformGlobalProducedAxisBanks.widths_ofFn
#print axioms ExactFourierCircuits.UniformGlobalProducedAxisBanks.widths_ofFn._simp_1_1

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformGlobalProducedAxisBanks.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

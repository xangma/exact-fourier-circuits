import UniformFinalDataClockProductResult
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result.cache
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result.casesOn
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result.clockSaved
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result.entry
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result.frame
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result.mk
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result.mk._flat_ctor
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result.movement
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result.numeric
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result.pc
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result.rec
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result.recOn
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result.reindex
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result.runtime
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result.saved
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result.source
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result.standard
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result.table
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result.thirdNumeric
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result.thirdSaved
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.Result.transform
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.budget
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.product
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.product_eq
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.savedBase
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.sourceBase
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.targetBase
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.thirdValues
#print axioms ExactFourierCircuits.UniformFinalDataClockProduct.volume

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformFinalDataClockProductResult.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

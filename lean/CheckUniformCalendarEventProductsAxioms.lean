import UniformCalendarEventProducts
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformCalendarEventProducts.embedded_diagonal_off
#print axioms ExactFourierCircuits.UniformCalendarEventProducts.embedded_diagonal_on
#print axioms ExactFourierCircuits.UniformCalendarEventProducts.family_diagonal_product
#print axioms ExactFourierCircuits.UniformCalendarEventProducts.foldValues_perm
#print axioms ExactFourierCircuits.UniformCalendarEventProducts.foldValues_product
#print axioms ExactFourierCircuits.UniformCalendarEventProducts.product_get
#print axioms ExactFourierCircuits.UniformGlobalCalendarDispatch.foldValues.eq_1
#print axioms ExactFourierCircuits.UniformGlobalCalendarDispatch.foldValues.eq_2
#print axioms ExactFourierCircuits.UniformGlobalCalendarDispatch.foldValues.eq_def

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformCalendarEventProducts.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

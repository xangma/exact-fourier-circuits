import UniformRecursiveNamedPreparationReserve
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformRecursiveNamedPreparationReserve.actual_producer_bound
#print axioms ExactFourierCircuits.UniformRecursiveNamedPreparationReserve.actual_producer_polynomial
#print axioms ExactFourierCircuits.UniformRecursiveNamedPreparationReserve.preparationTicks
#print axioms ExactFourierCircuits.UniformRecursiveNamedPreparationReserve.preparationTicks_lower
#print axioms ExactFourierCircuits.UniformRecursiveNamedPreparationReserve.producer_adapter
#print axioms ExactFourierCircuits.UniformRecursiveNamedPreparationReserve.producer_adapter._proof_1_1

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformRecursiveNamedPreparationReserve.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

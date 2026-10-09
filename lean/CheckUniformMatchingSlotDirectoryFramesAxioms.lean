import UniformMatchingSlotDirectoryFrames
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformLocalMatchingSlotDirectory.driverFree
#print axioms ExactFourierCircuits.UniformLocalMatchingSlotDirectory.driverFree._sparseCasesOn_1
#print axioms ExactFourierCircuits.UniformLocalMatchingSlotDirectory.driverFree._sparseCasesOn_1.else_eq
#print axioms ExactFourierCircuits.UniformLocalMatchingSlotDirectory.driverFree.eq_1
#print axioms ExactFourierCircuits.UniformLocalMatchingSlotDirectory.driverFree.eq_2
#print axioms ExactFourierCircuits.UniformLocalMatchingSlotDirectory.driverFree.eq_3
#print axioms ExactFourierCircuits.UniformLocalMatchingSlotDirectory.driverFree.eq_4
#print axioms ExactFourierCircuits.UniformLocalMatchingSlotDirectory.driverFree.eq_5
#print axioms ExactFourierCircuits.UniformLocalMatchingSlotDirectory.driverFree.match_1
#print axioms ExactFourierCircuits.UniformLocalMatchingSlotDirectory.driver_free
#print axioms ExactFourierCircuits.UniformLocalMatchingSlotDirectory.driver_keeps
#print axioms ExactFourierCircuits.UniformLocalMatchingSlotDirectory.driver_keeps._proof_1_7
#print axioms ExactFourierCircuits.UniformLocalMatchingSlotDirectory.execution_keeps_driver

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformMatchingSlotDirectoryFrames.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

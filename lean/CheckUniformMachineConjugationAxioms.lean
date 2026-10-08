import UniformMachineConjugation
import Lean

set_option autoImplicit false
set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformMachineConjugation.Allowed
#print axioms ExactFourierCircuits.UniformMachineConjugation.bounded_execution
#print axioms ExactFourierCircuits.UniformMachineConjugation.bounded_runs
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjResult
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjResult.eq_1
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjResult.eq_2
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjResult.eq_3
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjResult.match_1
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjResult_twice
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjScalar
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjScalar.eq_1
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjScalar_dependent
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjScalar_rational
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjScalar_twice
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjScalar_value
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjScalar_zero
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjState
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjState.eq_1
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjState_natHeap
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjState_natReg
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjState_next
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjState_output
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjState_outputs
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjState_pc
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjState_rootOrders
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjState_scalarHeap
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjState_scalarReg
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjState_setPC
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjState_storeNat
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjState_storeScalar
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjState_twice
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjState_writeNat
#print axioms ExactFourierCircuits.UniformMachineConjugation.conjState_writeScalar
#print axioms ExactFourierCircuits.UniformMachineConjugation.evalField_conjugate
#print axioms ExactFourierCircuits.UniformMachineConjugation.evalField_failure_iff
#print axioms ExactFourierCircuits.UniformMachineConjugation.executes
#print axioms ExactFourierCircuits.UniformMachineConjugation.instructionAllowed
#print axioms ExactFourierCircuits.UniformMachineConjugation.instructionAllowed._sparseCasesOn_1
#print axioms ExactFourierCircuits.UniformMachineConjugation.instructionAllowed._sparseCasesOn_1.else_eq
#print axioms ExactFourierCircuits.UniformMachineConjugation.instructionAllowed.eq_1
#print axioms ExactFourierCircuits.UniformMachineConjugation.instructionAllowed.eq_2
#print axioms ExactFourierCircuits.UniformMachineConjugation.instructionAllowed.eq_3
#print axioms ExactFourierCircuits.UniformMachineConjugation.instructionAllowed.match_1
#print axioms ExactFourierCircuits.UniformMachineConjugation.map_update
#print axioms ExactFourierCircuits.UniformMachineConjugation.runs
#print axioms ExactFourierCircuits.UniformMachineConjugation.step_conjugate
#print axioms ExactFourierCircuits.UniformMachineConjugation.step_failure_iff
#print axioms ExactFourierCircuits.UniformMachineConjugation.wordBound
#print axioms ExactFourierCircuits.UniformMachineConjugation.wordBound_iff

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformMachineConjugation.".isPrefixOf name.toString then
   let axioms ← collectAxioms name
   logInfo m!"'{name}' depends on axioms: {axioms.toList}"
   for ax in axioms do
    unless ax == `propext || ax == `Quot.sound || ax == `Classical.choice do
     throwError m!"Forbidden axiom {ax} in {name}"

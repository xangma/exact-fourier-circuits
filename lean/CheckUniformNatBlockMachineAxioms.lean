import UniformNatBlockMachine
import Lean
set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformNatBlockMachine.BlockAt
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op._sizeOf_1
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op._sizeOf_inst
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.apply
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.apply.eq_1
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.apply.eq_2
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.apply.eq_3
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.apply.eq_4
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.apply.match_1
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.apply_pc
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.binary
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.binary.elim
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.binary.inj
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.binary.injEq
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.binary.noConfusion
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.binary.sizeOf_spec
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.bound
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.casesOn
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.code
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.code.eq_1
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.code.eq_2
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.code.eq_3
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.code.eq_4
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.code.match_1
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.ctorElim
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.ctorElimType
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.ctorIdx
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.literal
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.literal.elim
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.literal.inj
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.literal.injEq
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.literal.noConfusion
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.literal.sizeOf_spec
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.load
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.load.elim
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.load.inj
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.load.injEq
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.load.noConfusion
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.load.sizeOf_spec
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.noConfusion
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.noConfusionType
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.peak
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.peak.eq_1
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.peak.eq_2
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.peak.eq_3
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.peak.eq_4
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.readable
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.readable._sparseCasesOn_1
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.readable._sparseCasesOn_1.else_eq
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.readable.eq_1
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.readable.eq_2
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.readable.eq_3
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.readable.match_1
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.rec
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.recOn
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.step
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.store
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.store.elim
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.store.inj
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.store.injEq
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.store.noConfusion
#print axioms ExactFourierCircuits.UniformNatBlockMachine.Op.store.sizeOf_spec
#print axioms ExactFourierCircuits.UniformNatBlockMachine.applyBlock
#print axioms ExactFourierCircuits.UniformNatBlockMachine.applyBlock._f
#print axioms ExactFourierCircuits.UniformNatBlockMachine.applyBlock._sunfold
#print axioms ExactFourierCircuits.UniformNatBlockMachine.applyBlock._unsafe_rec
#print axioms ExactFourierCircuits.UniformNatBlockMachine.applyBlock.eq_1
#print axioms ExactFourierCircuits.UniformNatBlockMachine.applyBlock.eq_2
#print axioms ExactFourierCircuits.UniformNatBlockMachine.applyBlock.eq_def
#print axioms ExactFourierCircuits.UniformNatBlockMachine.applyBlock.match_1
#print axioms ExactFourierCircuits.UniformNatBlockMachine.block_runs
#print axioms ExactFourierCircuits.UniformNatBlockMachine.block_runs._proof_1_1
#print axioms ExactFourierCircuits.UniformNatBlockMachine.block_runs._proof_1_2
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_1
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_10
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_11
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_12
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_13
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_14
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_15
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_16
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_17
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_18
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_19
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_2
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_20
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_21
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_22
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_23
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_24
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_25
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_26
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_3
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_4
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_5
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_6
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_7
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_8
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq._proof_9
#print axioms ExactFourierCircuits.UniformNatBlockMachine.instDecidableEqOp.decEq.match_1
#print axioms ExactFourierCircuits.UniformNatBlockMachine.peak
#print axioms ExactFourierCircuits.UniformNatBlockMachine.peak._f
#print axioms ExactFourierCircuits.UniformNatBlockMachine.peak._sunfold
#print axioms ExactFourierCircuits.UniformNatBlockMachine.peak._unsafe_rec
#print axioms ExactFourierCircuits.UniformNatBlockMachine.peak.eq_1
#print axioms ExactFourierCircuits.UniformNatBlockMachine.peak.eq_2
#print axioms ExactFourierCircuits.UniformNatBlockMachine.peak.eq_def
#print axioms ExactFourierCircuits.UniformNatBlockMachine.readable
#print axioms ExactFourierCircuits.UniformNatBlockMachine.readable._f
#print axioms ExactFourierCircuits.UniformNatBlockMachine.readable._sunfold
#print axioms ExactFourierCircuits.UniformNatBlockMachine.readable._unsafe_rec
#print axioms ExactFourierCircuits.UniformNatBlockMachine.readable.eq_1
#print axioms ExactFourierCircuits.UniformNatBlockMachine.readable.eq_2
#print axioms ExactFourierCircuits.UniformNatBlockMachine.readable.eq_def

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformNatBlockMachine.".isPrefixOf name.toString then
   let axioms ← collectAxioms name
   for ax in axioms do
    unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
     throwError m!"Nonstandard axiom {ax} in {name}"
   logInfo m!"{name} depends on axioms: {axioms.toList}"

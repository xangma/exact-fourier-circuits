import UniformNatHeaderFrame
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformNatHeaderFrame.block_natReg
#print axioms ExactFourierCircuits.UniformNatHeaderFrame.keeps
#print axioms ExactFourierCircuits.UniformNatHeaderFrame.keeps.eq_1
#print axioms ExactFourierCircuits.UniformNatHeaderFrame.keeps.eq_2
#print axioms ExactFourierCircuits.UniformNatHeaderFrame.keeps.eq_3
#print axioms ExactFourierCircuits.UniformNatHeaderFrame.keeps.eq_4
#print axioms ExactFourierCircuits.UniformNatHeaderFrame.keeps.match_1
#print axioms ExactFourierCircuits.UniformNatHeaderFrame.op_natReg

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformNatHeaderFrame.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

import UniformSyntacticNatFrame
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformSyntacticNatFrame.Avoids
#print axioms ExactFourierCircuits.UniformSyntacticNatFrame.avoids_append
#print axioms ExactFourierCircuits.UniformSyntacticNatFrame.avoids_flatMap
#print axioms ExactFourierCircuits.UniformSyntacticNatFrame.avoids_keeps
#print axioms ExactFourierCircuits.UniformSyntacticNatFrame.avoids_map_relocate
#print axioms ExactFourierCircuits.UniformSyntacticNatFrame.boundedExecution_preserves
#print axioms ExactFourierCircuits.UniformSyntacticNatFrame.boundedRuns_preserves
#print axioms ExactFourierCircuits.UniformSyntacticNatFrame.execution_preserves
#print axioms ExactFourierCircuits.UniformSyntacticNatFrame.natDst
#print axioms ExactFourierCircuits.UniformSyntacticNatFrame.natDst._sparseCasesOn_1
#print axioms ExactFourierCircuits.UniformSyntacticNatFrame.natDst._sparseCasesOn_1.else_eq
#print axioms ExactFourierCircuits.UniformSyntacticNatFrame.natDst.eq_1
#print axioms ExactFourierCircuits.UniformSyntacticNatFrame.natDst.eq_2
#print axioms ExactFourierCircuits.UniformSyntacticNatFrame.natDst.eq_3
#print axioms ExactFourierCircuits.UniformSyntacticNatFrame.natDst.eq_4
#print axioms ExactFourierCircuits.UniformSyntacticNatFrame.natDst.eq_5
#print axioms ExactFourierCircuits.UniformSyntacticNatFrame.natDst.match_1
#print axioms ExactFourierCircuits.UniformSyntacticNatFrame.relocate_dst
#print axioms ExactFourierCircuits.UniformSyntacticNatFrame.runs_preserves
#print axioms ExactFourierCircuits.UniformSyntacticNatFrame.step_preserves

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformSyntacticNatFrame.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

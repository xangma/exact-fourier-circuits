import UniformColoring
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformColoring.Conflict
#print axioms ExactFourierCircuits.UniformColoring.Conflict.eq_1
#print axioms ExactFourierCircuits.UniformColoring.DegreeBound
#print axioms ExactFourierCircuits.UniformColoring.Edge
#print axioms ExactFourierCircuits.UniformColoring.Edge._sizeOf_1
#print axioms ExactFourierCircuits.UniformColoring.Edge._sizeOf_inst
#print axioms ExactFourierCircuits.UniformColoring.Edge.casesOn
#print axioms ExactFourierCircuits.UniformColoring.Edge.ctorIdx
#print axioms ExactFourierCircuits.UniformColoring.Edge.different
#print axioms ExactFourierCircuits.UniformColoring.Edge.left
#print axioms ExactFourierCircuits.UniformColoring.Edge.mk
#print axioms ExactFourierCircuits.UniformColoring.Edge.mk._flat_ctor
#print axioms ExactFourierCircuits.UniformColoring.Edge.mk.congr_simp
#print axioms ExactFourierCircuits.UniformColoring.Edge.mk.inj
#print axioms ExactFourierCircuits.UniformColoring.Edge.mk.injEq
#print axioms ExactFourierCircuits.UniformColoring.Edge.mk.noConfusion
#print axioms ExactFourierCircuits.UniformColoring.Edge.mk.sizeOf_spec
#print axioms ExactFourierCircuits.UniformColoring.Edge.noConfusion
#print axioms ExactFourierCircuits.UniformColoring.Edge.noConfusionType
#print axioms ExactFourierCircuits.UniformColoring.Edge.rec
#print axioms ExactFourierCircuits.UniformColoring.Edge.recOn
#print axioms ExactFourierCircuits.UniformColoring.Edge.right
#print axioms ExactFourierCircuits.UniformColoring.Good
#print axioms ExactFourierCircuits.UniformColoring.Incident
#print axioms ExactFourierCircuits.UniformColoring.Incident.eq_1
#print axioms ExactFourierCircuits.UniformColoring.coloring
#print axioms ExactFourierCircuits.UniformColoring.coloring_bound
#print axioms ExactFourierCircuits.UniformColoring.coloring_proper
#print axioms ExactFourierCircuits.UniformColoring.conflict_symm
#print axioms ExactFourierCircuits.UniformColoring.conflict_symm._simp_1_3
#print axioms ExactFourierCircuits.UniformColoring.earlierColors
#print axioms ExactFourierCircuits.UniformColoring.earlierColors_card
#print axioms ExactFourierCircuits.UniformColoring.earlierNeighbors
#print axioms ExactFourierCircuits.UniformColoring.earlierNeighbors.eq_1
#print axioms ExactFourierCircuits.UniformColoring.firstFree
#print axioms ExactFourierCircuits.UniformColoring.firstFree.eq_1
#print axioms ExactFourierCircuits.UniformColoring.firstFree_spec
#print axioms ExactFourierCircuits.UniformColoring.greedy
#print axioms ExactFourierCircuits.UniformColoring.greedy._f
#print axioms ExactFourierCircuits.UniformColoring.greedy._sunfold
#print axioms ExactFourierCircuits.UniformColoring.greedy._unsafe_rec
#print axioms ExactFourierCircuits.UniformColoring.greedy.eq_1
#print axioms ExactFourierCircuits.UniformColoring.greedy.eq_2
#print axioms ExactFourierCircuits.UniformColoring.greedy.eq_def
#print axioms ExactFourierCircuits.UniformColoring.greedy.match_1
#print axioms ExactFourierCircuits.UniformColoring.greedy_good
#print axioms ExactFourierCircuits.UniformColoring.greedy_good._proof_1_1
#print axioms ExactFourierCircuits.UniformColoring.greedy_good._proof_1_10
#print axioms ExactFourierCircuits.UniformColoring.greedy_good._proof_1_11
#print axioms ExactFourierCircuits.UniformColoring.greedy_good._proof_1_2
#print axioms ExactFourierCircuits.UniformColoring.greedy_good._proof_1_3
#print axioms ExactFourierCircuits.UniformColoring.greedy_good._proof_1_4
#print axioms ExactFourierCircuits.UniformColoring.greedy_good._proof_1_5
#print axioms ExactFourierCircuits.UniformColoring.greedy_good._proof_1_6
#print axioms ExactFourierCircuits.UniformColoring.greedy_good._simp_1_8
#print axioms ExactFourierCircuits.UniformColoring.greedy_good._simp_1_9
#print axioms ExactFourierCircuits.UniformColoring.greedy_next
#print axioms ExactFourierCircuits.UniformColoring.incidentEdges
#print axioms ExactFourierCircuits.UniformColoring.instDecidableConflict
#print axioms ExactFourierCircuits.UniformColoring.instDecidableConflict._aux_1
#print axioms ExactFourierCircuits.UniformColoring.instDecidableIncident
#print axioms ExactFourierCircuits.UniformColoring.instDecidableIncident._aux_1
#print axioms ExactFourierCircuits.UniformColoring.layer
#print axioms ExactFourierCircuits.UniformColoring.layer.eq_1
#print axioms ExactFourierCircuits.UniformColoring.layer_disjoint
#print axioms ExactFourierCircuits.UniformColoring.layer_nodup
#print axioms ExactFourierCircuits.UniformColoring.layers
#print axioms ExactFourierCircuits.UniformColoring.layers.eq_1
#print axioms ExactFourierCircuits.UniformColoring.layers_length
#print axioms ExactFourierCircuits.UniformColoring.mem_layer
#print axioms ExactFourierCircuits.UniformColoring.mem_layer._simp_1
#print axioms ExactFourierCircuits.UniformColoring.neighbors_card
#print axioms ExactFourierCircuits.UniformColoring.neighbors_card._proof_1_1
#print axioms ExactFourierCircuits.UniformColoring.neighbors_subset
#print axioms ExactFourierCircuits.UniformColoring.neighbors_subset._proof_1_4
#print axioms ExactFourierCircuits.UniformColoring.neighbors_subset._simp_1_2
#print axioms ExactFourierCircuits.UniformColoring.neighbors_subset._simp_1_3
#print axioms ExactFourierCircuits.UniformColoring.printedEdges
#print axioms ExactFourierCircuits.UniformColoring.printedEdges.eq_1
#print axioms ExactFourierCircuits.UniformColoring.printedLayers
#print axioms ExactFourierCircuits.UniformColoring.printedLayers_length
#print axioms ExactFourierCircuits.UniformColoring.printed_matching
#print axioms ExactFourierCircuits.UniformColoring.printed_matching._simp_1_5
#print axioms ExactFourierCircuits.UniformColoring.printed_matching._simp_1_6
#print axioms ExactFourierCircuits.UniformColoring.printed_matching._simp_1_7
#print axioms ExactFourierCircuits.UniformColoring.same_color_disjoint
#print axioms ExactFourierCircuits.UniformColoring.shearEdge
#print axioms ExactFourierCircuits.UniformColoring.shearEdge.eq_1
#print axioms ExactFourierCircuits.UniformColoring.unique_layer

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformColoring.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

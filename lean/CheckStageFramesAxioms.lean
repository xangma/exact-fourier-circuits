import StageFrames
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.BinaryResiduals.label3.eq_1
#print axioms ExactFourierCircuits.BinaryResiduals.residual.eq_1
#print axioms ExactFourierCircuits.StageFrames.Axis
#print axioms ExactFourierCircuits.StageFrames.Cube
#print axioms ExactFourierCircuits.StageFrames.EmptyCoordinates
#print axioms ExactFourierCircuits.StageFrames.PhysicalCoordinates
#print axioms ExactFourierCircuits.StageFrames.addressCoordinates
#print axioms ExactFourierCircuits.StageFrames.addressCoordinates._proof_1
#print axioms ExactFourierCircuits.StageFrames.appendCoordinates
#print axioms ExactFourierCircuits.StageFrames.appendCoordinates.eq_1
#print axioms ExactFourierCircuits.StageFrames.append_tripleTensor
#print axioms ExactFourierCircuits.StageFrames.boundary_0_X
#print axioms ExactFourierCircuits.StageFrames.boundary_0_Y
#print axioms ExactFourierCircuits.StageFrames.boundary_1_X
#print axioms ExactFourierCircuits.StageFrames.boundary_1_Y
#print axioms ExactFourierCircuits.StageFrames.columnCoordinates
#print axioms ExactFourierCircuits.StageFrames.column_coordinate_card
#print axioms ExactFourierCircuits.StageFrames.consecutive_boundaries
#print axioms ExactFourierCircuits.StageFrames.coordinates
#print axioms ExactFourierCircuits.StageFrames.coordinates._proof_1
#print axioms ExactFourierCircuits.StageFrames.coordinates._proof_2
#print axioms ExactFourierCircuits.StageFrames.coordinates._proof_3
#print axioms ExactFourierCircuits.StageFrames.coordinates._proof_4
#print axioms ExactFourierCircuits.StageFrames.coordinates._proof_5
#print axioms ExactFourierCircuits.StageFrames.coordinates.eq_1
#print axioms ExactFourierCircuits.StageFrames.coordinates_apply
#print axioms ExactFourierCircuits.StageFrames.coordinates_dot
#print axioms ExactFourierCircuits.StageFrames.coordinates_symm_apply
#print axioms ExactFourierCircuits.StageFrames.coordinates_tensor_assoc
#print axioms ExactFourierCircuits.StageFrames.coordinates_tensor_product
#print axioms ExactFourierCircuits.StageFrames.coordinates_unit_left
#print axioms ExactFourierCircuits.StageFrames.coordinates_weight
#print axioms ExactFourierCircuits.StageFrames.directions
#print axioms ExactFourierCircuits.StageFrames.directions.eq_1
#print axioms ExactFourierCircuits.StageFrames.directions_norm
#print axioms ExactFourierCircuits.StageFrames.emptyVector
#print axioms ExactFourierCircuits.StageFrames.emptyVector_characteristic
#print axioms ExactFourierCircuits.StageFrames.emptyVector_line
#print axioms ExactFourierCircuits.StageFrames.emptyVector_norm
#print axioms ExactFourierCircuits.StageFrames.emptyVector_perp
#print axioms ExactFourierCircuits.StageFrames.factor_complement_basis
#print axioms ExactFourierCircuits.StageFrames.firstCoordinates
#print axioms ExactFourierCircuits.StageFrames.firstCoordinates.eq_1
#print axioms ExactFourierCircuits.StageFrames.first_space_tensor
#print axioms ExactFourierCircuits.StageFrames.fullVector
#print axioms ExactFourierCircuits.StageFrames.fullVector.eq_1
#print axioms ExactFourierCircuits.StageFrames.future_line_factor
#print axioms ExactFourierCircuits.StageFrames.incomingX
#print axioms ExactFourierCircuits.StageFrames.incomingX.eq_1
#print axioms ExactFourierCircuits.StageFrames.incomingX.eq_2
#print axioms ExactFourierCircuits.StageFrames.incomingX.eq_3
#print axioms ExactFourierCircuits.StageFrames.incomingX.match_1
#print axioms ExactFourierCircuits.StageFrames.incomingY
#print axioms ExactFourierCircuits.StageFrames.incomingY.eq_1
#print axioms ExactFourierCircuits.StageFrames.incomingY.eq_2
#print axioms ExactFourierCircuits.StageFrames.incomingY.eq_3
#print axioms ExactFourierCircuits.StageFrames.lastCoordinates
#print axioms ExactFourierCircuits.StageFrames.lastCoordinates.eq_1
#print axioms ExactFourierCircuits.StageFrames.mem_space
#print axioms ExactFourierCircuits.StageFrames.mem_tensorSpace_line
#print axioms ExactFourierCircuits.StageFrames.orth_line
#print axioms ExactFourierCircuits.StageFrames.outgoingX
#print axioms ExactFourierCircuits.StageFrames.outgoingX.eq_1
#print axioms ExactFourierCircuits.StageFrames.outgoingX.eq_2
#print axioms ExactFourierCircuits.StageFrames.outgoingX.eq_3
#print axioms ExactFourierCircuits.StageFrames.outgoingY
#print axioms ExactFourierCircuits.StageFrames.outgoingY.eq_1
#print axioms ExactFourierCircuits.StageFrames.outgoingY.eq_2
#print axioms ExactFourierCircuits.StageFrames.outgoingY.eq_3
#print axioms ExactFourierCircuits.StageFrames.outgoing_perp
#print axioms ExactFourierCircuits.StageFrames.physicalIncomingX
#print axioms ExactFourierCircuits.StageFrames.physicalIncomingX.eq_1
#print axioms ExactFourierCircuits.StageFrames.physicalIncomingY
#print axioms ExactFourierCircuits.StageFrames.physicalIncomingY.eq_1
#print axioms ExactFourierCircuits.StageFrames.physicalOutgoingX
#print axioms ExactFourierCircuits.StageFrames.physicalOutgoingX.eq_1
#print axioms ExactFourierCircuits.StageFrames.physicalOutgoingY
#print axioms ExactFourierCircuits.StageFrames.physicalOutgoingY.eq_1
#print axioms ExactFourierCircuits.StageFrames.physical_full_tripleTensor
#print axioms ExactFourierCircuits.StageFrames.physical_sink
#print axioms ExactFourierCircuits.StageFrames.physical_source
#print axioms ExactFourierCircuits.StageFrames.prefix_outgoing_perp
#print axioms ExactFourierCircuits.StageFrames.prependCoordinates
#print axioms ExactFourierCircuits.StageFrames.prependCoordinates.eq_1
#print axioms ExactFourierCircuits.StageFrames.prepend_tripleTensor
#print axioms ExactFourierCircuits.StageFrames.sink_X
#print axioms ExactFourierCircuits.StageFrames.sink_Y
#print axioms ExactFourierCircuits.StageFrames.source_X
#print axioms ExactFourierCircuits.StageFrames.source_Y
#print axioms ExactFourierCircuits.StageFrames.space
#print axioms ExactFourierCircuits.StageFrames.space._proof_1
#print axioms ExactFourierCircuits.StageFrames.space_assoc_line
#print axioms ExactFourierCircuits.StageFrames.space_bot
#print axioms ExactFourierCircuits.StageFrames.space_bot._simp_1_1
#print axioms ExactFourierCircuits.StageFrames.space_line
#print axioms ExactFourierCircuits.StageFrames.space_perp
#print axioms ExactFourierCircuits.StageFrames.space_symm_cancel
#print axioms ExactFourierCircuits.StageFrames.space_symm_cancel._simp_1_1
#print axioms ExactFourierCircuits.StageFrames.space_tensor_line
#print axioms ExactFourierCircuits.StageFrames.space_top
#print axioms ExactFourierCircuits.StageFrames.space_top._simp_1_1
#print axioms ExactFourierCircuits.StageFrames.space_trans
#print axioms ExactFourierCircuits.StageFrames.space_trans._simp_1_1
#print axioms ExactFourierCircuits.StageFrames.space_unit_right
#print axioms ExactFourierCircuits.StageFrames.tensorRight
#print axioms ExactFourierCircuits.StageFrames.tensorSpace_bot_left
#print axioms ExactFourierCircuits.StageFrames.tensorSpace_line_line
#print axioms ExactFourierCircuits.StageFrames.tensorSpace_line_right
#print axioms ExactFourierCircuits.StageFrames.tripleCoordinates
#print axioms ExactFourierCircuits.StageFrames.tripleCoordinates._proof_1
#print axioms ExactFourierCircuits.StageFrames.tripleCoordinates._proof_2
#print axioms ExactFourierCircuits.StageFrames.tripleCoordinates._proof_3
#print axioms ExactFourierCircuits.StageFrames.tripleCoordinates.eq_1
#print axioms ExactFourierCircuits.StageFrames.triple_stage_boundaries

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.StageFrames.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

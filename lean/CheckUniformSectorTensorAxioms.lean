import UniformSectorTensor
import Lean

set_option linter.auxLemma false

#print axioms ExactFourierCircuits.UniformSectorPacking.combine.eq_1
#print axioms ExactFourierCircuits.UniformSectorPacking.combine.eq_2
#print axioms ExactFourierCircuits.UniformSectorPacking.combine.eq_def
#print axioms ExactFourierCircuits.UniformSectorPacking.originalEquiv.eq_1
#print axioms ExactFourierCircuits.UniformSectorPacking.packingPermutation.eq_1
#print axioms ExactFourierCircuits.UniformSectorTensor.binaryDigits
#print axioms ExactFourierCircuits.UniformSectorTensor.binaryDigits._f
#print axioms ExactFourierCircuits.UniformSectorTensor.binaryDigits._sunfold
#print axioms ExactFourierCircuits.UniformSectorTensor.binaryDigits._unsafe_rec
#print axioms ExactFourierCircuits.UniformSectorTensor.binaryDigits.eq_1
#print axioms ExactFourierCircuits.UniformSectorTensor.binaryDigits.eq_2
#print axioms ExactFourierCircuits.UniformSectorTensor.binaryDigits.eq_def
#print axioms ExactFourierCircuits.UniformSectorTensor.binaryDigits.match_1
#print axioms ExactFourierCircuits.UniformSectorTensor.binaryDigits_length
#print axioms ExactFourierCircuits.UniformSectorTensor.binaryDigits_lt_two
#print axioms ExactFourierCircuits.UniformSectorTensor.binaryDigits_lt_two._simp_1_4
#print axioms ExactFourierCircuits.UniformSectorTensor.binaryEntry
#print axioms ExactFourierCircuits.UniformSectorTensor.binaryEntry.eq_1
#print axioms ExactFourierCircuits.UniformSectorTensor.blockChoiceDecEq
#print axioms ExactFourierCircuits.UniformSectorTensor.blockChoiceDecEq._aux_1
#print axioms ExactFourierCircuits.UniformSectorTensor.blockChoiceDecEq._aux_3
#print axioms ExactFourierCircuits.UniformSectorTensor.blockEntry
#print axioms ExactFourierCircuits.UniformSectorTensor.blockEntry.eq_1
#print axioms ExactFourierCircuits.UniformSectorTensor.blockEntry_one
#print axioms ExactFourierCircuits.UniformSectorTensor.blockEntry_two
#print axioms ExactFourierCircuits.UniformSectorTensor.localEntry
#print axioms ExactFourierCircuits.UniformSectorTensor.localEntry_off
#print axioms ExactFourierCircuits.UniformSectorTensor.localEntry_same
#print axioms ExactFourierCircuits.UniformSectorTensor.localTensor
#print axioms ExactFourierCircuits.UniformSectorTensor.localTensor._f
#print axioms ExactFourierCircuits.UniformSectorTensor.localTensor._sunfold
#print axioms ExactFourierCircuits.UniformSectorTensor.localTensor._unsafe_rec
#print axioms ExactFourierCircuits.UniformSectorTensor.localTensor.eq_1
#print axioms ExactFourierCircuits.UniformSectorTensor.localTensor.eq_2
#print axioms ExactFourierCircuits.UniformSectorTensor.localTensor.eq_def
#print axioms ExactFourierCircuits.UniformSectorTensor.localTensor.match_1
#print axioms ExactFourierCircuits.UniformSectorTensor.localTensor_off
#print axioms ExactFourierCircuits.UniformSectorTensor.localTensor_same
#print axioms ExactFourierCircuits.UniformSectorTensor.originalTensor
#print axioms ExactFourierCircuits.UniformSectorTensor.originalTensor.eq_1
#print axioms ExactFourierCircuits.UniformSectorTensor.originalTensor_coordinates
#print axioms ExactFourierCircuits.UniformSectorTensor.originalTensor_sectors
#print axioms ExactFourierCircuits.UniformSectorTensor.packedTensor
#print axioms ExactFourierCircuits.UniformSectorTensor.packedTensor.eq_1
#print axioms ExactFourierCircuits.UniformSectorTensor.packing_tensor
#print axioms ExactFourierCircuits.UniformSectorTensor.sectorMatrix
#print axioms ExactFourierCircuits.UniformSectorTensor.sectorTensor
#print axioms ExactFourierCircuits.UniformSectorTensor.sectorTensor._f
#print axioms ExactFourierCircuits.UniformSectorTensor.sectorTensor._sunfold
#print axioms ExactFourierCircuits.UniformSectorTensor.sectorTensor._unsafe_rec
#print axioms ExactFourierCircuits.UniformSectorTensor.sectorTensor.eq_1
#print axioms ExactFourierCircuits.UniformSectorTensor.sectorTensor.eq_2
#print axioms ExactFourierCircuits.UniformSectorTensor.sectorTensor.eq_def
#print axioms ExactFourierCircuits.UniformSectorTensor.sectorTensor.match_1
#print axioms ExactFourierCircuits.UniformSectorTensor.sectorTensor_binary
#print axioms ExactFourierCircuits.UniformTraversal.addressLayer.eq_1

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  if "_private.UniformSectorTensor.".isPrefixOf name.toString then
   let axs ← collectAxioms name
   logInfo m!"{name} depends on axioms: {axs.toList}"

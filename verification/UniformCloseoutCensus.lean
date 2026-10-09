import UniformGlobalEnvelope
import UniformTensorPhaseFusion
import UniformHeapDirectFourier
import UniformMatchingPhaseFusion
import UniformMatchingAxisFusion
import UniformBinaryBatchCMachine
import UniformHeapDirectBatch
import UniformTranslatedMatchingRows
import UniformMatchingPhysicalDiagonal
import UniformSmallAxisFourierMachine
import UniformSmallAxesBudget
import UniformSmallAxisFourierPreservation
import UniformSmallAxesMachine
import UniformNativeTensorCoordinates
import UniformSmallAxesTensorAction
import UniformGlobalSavingRecordMachine
import UniformWholeSavedHeaders
import UniformGlobalMatchingScaleMachine
import UniformGlobalScalePoolMachine
import UniformGlobalMatchingPoolPreparation
import UniformGlobalMatchingScaleBankBridge
import UniformGlobalDiagonalPhasePreparation
import UniformGlobalMatchingDiagonalPreparation
import UniformAxisEdgeProducer
import UniformSeedEdgeRetention
import UniformAllAxisSeedEdgePreparation
import UniformResidualNativeCoordinates
import UniformResidualAddressToggleMachine
import UniformResidualFiberAddressMachine
import UniformResidualFiberTraversal
import UniformFixedNetworkMarkerMachine
import UniformResidualPivotMachine
import UniformResidualBasisMachine
import UniformResidualBasisExecution
import UniformResidualDescriptorBankMachine
import UniformResidualPermutation
import UniformResidualArrayCopyMachine
import UniformResidualPermutationPreparation
import UniformResidualGatherPreparation
import UniformSectorBatchDirectoryMachine
import UniformSectorMetadataCountBridge
import UniformProducedSectorBatchPreparation
import UniformSectorPaddingMachine
import UniformSectorPaddingPreparation
import UniformAllSectorPaddingMachine
import UniformProducedSectorPaddingPreparation
import Lean
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 let mods := ["UniformGlobalEnvelope", "UniformTensorPhaseFusion", "UniformHeapDirectFourier", "UniformMatchingPhaseFusion", "UniformMatchingAxisFusion", "UniformBinaryBatchCMachine", "UniformHeapDirectBatch", "UniformTranslatedMatchingRows", "UniformMatchingPhysicalDiagonal", "UniformSmallAxisFourierMachine", "UniformSmallAxesBudget", "UniformSmallAxisFourierPreservation", "UniformSmallAxesMachine", "UniformNativeTensorCoordinates", "UniformSmallAxesTensorAction", "UniformGlobalSavingRecordMachine", "UniformWholeSavedHeaders", "UniformGlobalMatchingScaleMachine", "UniformGlobalScalePoolMachine", "UniformGlobalMatchingPoolPreparation", "UniformGlobalMatchingScaleBankBridge", "UniformGlobalDiagonalPhasePreparation", "UniformGlobalMatchingDiagonalPreparation", "UniformAxisEdgeProducer", "UniformSeedEdgeRetention", "UniformAllAxisSeedEdgePreparation", "UniformResidualNativeCoordinates", "UniformResidualAddressToggleMachine", "UniformResidualFiberAddressMachine", "UniformResidualFiberTraversal", "UniformFixedNetworkMarkerMachine", "UniformResidualPivotMachine", "UniformResidualBasisMachine", "UniformResidualBasisExecution", "UniformResidualDescriptorBankMachine", "UniformResidualPermutation", "UniformResidualArrayCopyMachine", "UniformResidualPermutationPreparation", "UniformResidualGatherPreparation", "UniformSectorBatchDirectoryMachine", "UniformSectorMetadataCountBridge", "UniformProducedSectorBatchPreparation", "UniformSectorPaddingMachine", "UniformSectorPaddingPreparation", "UniformAllSectorPaddingMachine", "UniformProducedSectorPaddingPreparation"]
 let mut entries:Array Json:=#[]
 for (name, _) in env.constants.toList do
  if mods.any (fun m => ("ExactFourierCircuits."++m++".").isPrefixOf name.toString || ("_private."++m++".").isPrefixOf name.toString) then
   let axioms ← collectAxioms name
   for ax in axioms do
    unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
     throwError m!"Nonstandard axiom {ax} in {name}"
   entries:=entries.push (Json.mkObj [("name",toJson name.toString),("axioms",toJson (axioms.toList.map toString))])
 liftIO <| IO.FS.writeFile "../logs/uniform-closeout-foundations/census.json" (Json.compress (.arr entries))
 logInfo m!"Audited {entries.size} declarations in {mods.length} modules"

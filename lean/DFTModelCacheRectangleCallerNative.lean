import DFTModelCacheRectangleCallerFields
import DFTModelCacheRectangleMetadataSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheRectangleCaller
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalRectangleDescriptors UniformAllAxisSeedPreparation
noncomputable section

def genuineInput (n:ℕ) (j:Fin (axisCount n)) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (slot:UniformLocalCacheChronology.Slot) : Input.T :=
 input (radix n j) (UniformMasterRootMachine.order n) original.C original.negative original.constants
  (OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)) slot.depth slot.color slot.enabled q

theorem genuine_dimensions (n:ℕ) (j:Fin (axisCount n)) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (slot:UniformLocalCacheChronology.Slot) :
 (rowValue (genuineInput n j q original slot) 2,rowValue (genuineInput n j q original slot) 3)=
 (q.a,q.e) := by
 simp [genuineInput,rowValue,input,Tape.look,Tape.tab,Row.words]

/-- Both kernel metadata and physical matching geometry come from the same
seven-word descriptor, the same slot and the genuine selected-axis source.
The original offset is retained for the later ambient translation. -/
theorem argument_native (n:ℕ) (j:Fin (axisCount n)) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (c:UniformLocalCacheSlotHeaderMachine.Parameters)
 (slot:UniformLocalCacheChronology.Slot) :
 argumentValue (genuineInput n j q original slot) (preparedConfig q)=
 DFTModelCacheSelectedPhysicalRowsCaller.nativeInput
  (DFTModelCacheRectangleMetadata.chunk q original c slot)
  original.C original.negative original.constants
  (DFTModelCacheDisplacement.metadata (radix n j)
    (DFTModelCacheRectangleMetadata.kernel n j q original),
   (UniformMasterRootMachine.order n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))) := by
 obtain ⟨_,_,_,hK,ha,he,henabled,_,_,hd,hcolor⟩:=
  DFTModelCacheRectangleMetadata.chunk_fields q original c slot
 rw [DFTModelCacheSelectedPhysicalRowsCaller.nativeInput,
  DFTModelCacheRectangleMetadata.chunk_geometry,DFTModelCacheRectangleMetadata.metadata_eq]
 simp only [hK,ha,he,henabled,hd,hcolor]
 simp [genuineInput,argumentValue,controlValue,geometryValue,heightValue,metadataValue,
  rowValue,input,Tape.look,Tape.tab,Row.words,preparedConfig,DFTModelCacheTopology.config,
  gateValue,DFTModelCacheSelectedPhysicalRows.geom,DFTModelCacheHeightColorCaller.input,
  DFTModelCacheDisplacement.metadata,DFTModelCacheRectanglePreparation.parameters,
  DFTModelCacheRectanglePreparation.height,DFTModelCacheRectanglePreparation.width,
  DFTModelCacheTopology.exponent,UniformWorkspacePlanner.exponent,
  UniformWorkspacePlanner.gateCount_eq,UniformRadixTwoDAG.width_eq]

end
end ExactFourierCircuits.DFTModelCacheRectangleCaller

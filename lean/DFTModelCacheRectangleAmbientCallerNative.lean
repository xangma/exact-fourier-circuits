import DFTModelCacheRectangleAmbientCallerRun

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheRectangleAmbientCaller
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalRectangleDescriptors UniformAllAxisSeedPreparation
noncomputable section
attribute [local irreducible] Code.run program DFTModelCacheRectangleCaller.program
 DFTModelCacheSelectedPhysicalRowsCaller.program DFTModelCacheSelectedPhysicalRowsProduced.program
 DFTModelCacheSelectedPhysicalRows.program DFTModelCacheMatchingProduced.program

def genuineInput (ambient n:ℕ) (j:Fin (axisCount n)) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (slot:UniformLocalCacheChronology.Slot) : Input.T :=
 (ambient,DFTModelCacheRectangleCaller.genuineInput n j q original slot)

def mappedRows {B:ℕ} (p:UniformChunkMatchingPreparation.Parameters)
 (_layout:UniformChunkMatchingPreparation.Layout p B)
 (ha:p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (he:p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height)
 (C T P:ℕ) : Tape DFTModelCacheSelectedCoefficients.Row.T :=
 (run DFTModelCacheSelectedPhysicalRows.program
  (DFTModelCacheSelectedPhysicalRows.chunkGeometry p,
   DFTModelCacheSelectedPhysicalRows.rowTape
    (UniformChunkMatchingPreparation.selectedRows p (UniformChunkMatchingPreparation.crossWord p ha he)
     (UniformCrossShearTableMachine.locations _ C T P)))).val

theorem argument_native {B:ℕ} (ambient n:ℕ) (j:Fin (axisCount n)) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (c:UniformLocalCacheSlotHeaderMachine.Parameters)
 (slot:UniformLocalCacheChronology.Slot)
 (source:DFTModelCacheRectanglePreparation.ProducedRow (radix n j) q)
 (layout:UniformChunkMatchingPreparation.Layout (DFTModelCacheRectangleMetadata.chunk q original c slot) B)
 (height:slot.depth≤8*DFTModelCacheRectanglePreparation.height q+6) :
 let p:=DFTModelCacheRectangleMetadata.chunk q original c slot
 let ha: p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height :=
  (DFTModelCacheRectangleMetadata.chunk_widths source original c slot).1
 let he: p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height :=
  (DFTModelCacheRectangleMetadata.chunk_widths source original c slot).2
 let raw:=(DFTModelCacheDisplacement.metadata (radix n j)
   (DFTModelCacheRectangleMetadata.kernel n j q original),
  (UniformMasterRootMachine.order n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)))
 argumentValue (ambient,(run DFTModelCacheRectangleCaller.program
  (DFTModelCacheRectangleCaller.genuineInput n j q original slot)).val)=
 DFTModelCacheAmbientPool.args q.offset ambient p.height.K
  original.C original.negative original.constants raw
  (mappedRows p layout ha he original.C original.negative original.constants) := by
 dsimp only
 let p:=DFTModelCacheRectangleMetadata.chunk q original c slot
 have widths:=DFTModelCacheRectangleMetadata.chunk_widths source original c slot
 let raw:=(DFTModelCacheDisplacement.metadata (radix n j)
   (DFTModelCacheRectangleMetadata.kernel n j q original),
  (UniformMasterRootMachine.order n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)))
 have localRetained:
  localInputValue (ambient,(run DFTModelCacheRectangleCaller.program
   (DFTModelCacheRectangleCaller.genuineInput n j q original slot)).val)=
  DFTModelCacheMatchingProduced.args p.radix p.height.K
   original.C original.negative original.constants raw
   (mappedRows p layout widths.1 widths.2 original.C original.negative original.constants) := by
  unfold localInputValue
  rw [DFTModelCacheRectangleCaller.genuine_value n j q original c slot]
  change (run DFTModelCacheSelectedPhysicalRowsCaller.program
   (DFTModelCacheSelectedPhysicalRowsCaller.nativeInput p original.C original.negative original.constants raw)).val.2.1.1.1.1=_
  rw [DFTModelCacheSelectedPhysicalRowsCaller.program_run,
   DFTModelCacheSelectedPhysicalRowsCaller.native_argument p
    (DFTModelCacheRectangleMetadata.chunk_computed q original c slot)
    widths.1 widths.2 height original.C original.negative original.constants raw,
   DFTModelCacheSelectedPhysicalRowsProduced.program_run,
   DFTModelCacheSelectedPhysicalRowsProduced.nativeArgument,
   DFTModelCacheMatchingProduced.retained]
  rfl
 unfold argumentValue
 rw [localRetained,DFTModelCacheRectangleCaller.genuine_value n j q original c slot]
 change (DFTModelCacheRectangleCaller.rowValue
  (DFTModelCacheRectangleCaller.genuineInput n j q original slot) 1,_)=_
 unfold DFTModelCacheRectangleCaller.genuineInput
 rw [(DFTModelCacheRectangleCaller.input_rows (radix n j) (UniformMasterRootMachine.order n)
  original.C original.negative original.constants (OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))
  slot.depth slot.color slot.enabled q).2.1]
 rfl

end
end ExactFourierCircuits.DFTModelCacheRectangleAmbientCaller

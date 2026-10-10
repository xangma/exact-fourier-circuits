import DFTModelCacheRectangleCallerCorrect

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheRectangleCaller
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalRectangleDescriptors UniformAllAxisSeedPreparation
noncomputable section
attribute [local irreducible] Code.run program DFTModelCacheSelectedPhysicalRowsCaller.program

def peakBudget (n:ℕ) (j:Fin (axisCount n)) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (c:UniformLocalCacheSlotHeaderMachine.Parameters)
 (slot:UniformLocalCacheChronology.Slot) (M:ℕ) : ℕ :=
 max (max 3 (4*(q.a+q.e)+2)) (max (argumentPeak (preparedConfig q))
 (DFTModelCacheSelectedPhysicalRowsCaller.mixedPeakBudget
  (DFTModelCacheRectangleMetadata.chunk q original c slot) (radix n j)
  (UniformMasterRootMachine.order n) (DFTModelCacheRectangleMetadata.kernel n j q original)
  original.C original.negative original.constants M))

theorem peak {B:ℕ} (n:ℕ) (hn:0<n) (j:Fin (axisCount n)) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (c:UniformLocalCacheSlotHeaderMachine.Parameters)
 (slot:UniformLocalCacheChronology.Slot)
 (source:DFTModelCacheRectanglePreparation.ProducedRow (radix n j) q)
 (layout:UniformChunkMatchingPreparation.Layout (DFTModelCacheRectangleMetadata.chunk q original c slot) B)
 (height:slot.depth≤8*DFTModelCacheRectanglePreparation.height q+6)
 (positive:original.C+UniformToeplitzCrossDAG.bankSize (DFTModelCacheRectanglePreparation.height q)≤original.negative)
 (negative:original.negative+UniformToeplitzCrossDAG.bankSize (DFTModelCacheRectanglePreparation.height q)≤original.constants) :
 let p:=DFTModelCacheRectangleMetadata.chunk q original c slot
 let ha: p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height :=
  (DFTModelCacheRectangleMetadata.chunk_widths source original c slot).1
 let he: p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height :=
  (DFTModelCacheRectangleMetadata.chunk_widths source original c slot).2
 let W:=UniformChunkMatchingPreparation.crossWord p ha he
 (run program (genuineInput n j q original slot)).peak≤
 peakBudget n j q original c slot (UniformChunkMatchingPreparation.indices p W).length := by
 dsimp only
 let p:=DFTModelCacheRectangleMetadata.chunk q original c slot
 have widths:=DFTModelCacheRectangleMetadata.chunk_widths source original c slot
 obtain ⟨hD,hr,hN,h4⟩:=DFTModelCacheRectangleMetadata.selected_divisors n hn j q source
 have next:=DFTModelCacheSelectedPhysicalRowsCaller.mixed_peak p layout
  (DFTModelCacheRectangleMetadata.chunk_computed q original c slot) widths.1 widths.2 height
  (radix n j) (UniformMasterRootMachine.order n) (DFTModelCacheRectangleMetadata.kernel n j q original)
  (DFTModelCacheRectangleMetadata.kernel_shape n j q original source) rfl
  hD hr hN h4 original.C original.negative original.constants positive negative
 exact (genuine_peak n j q original c slot).trans
  (max_le_max (Nat.le_refl _) (max_le_max (Nat.le_refl _) next))

end
end ExactFourierCircuits.DFTModelCacheRectangleCaller

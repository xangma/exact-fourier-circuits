import DFTModelCacheRectangleAmbientCallerNative

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheRectangleAmbientCaller
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalRectangleDescriptors UniformAllAxisSeedPreparation
noncomputable section
attribute [local irreducible] Code.run DFTModelCacheAmbientPool.program

def ambientWorkBudget (n:ℕ) (j:Fin (axisCount n)) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (c:UniformLocalCacheSlotHeaderMachine.Parameters) (M:ℕ) : ℕ :=
 DFTModelCacheMatchingProduced.mixedWorkBudget c.ambient (radix n j)
  (UniformMasterRootMachine.order n) (DFTModelCacheRectangleMetadata.kernel n j q original)
  (DFTModelCacheRectanglePreparation.height q) M+49*M+41

def ambientPeakBudget (n:ℕ) (j:Fin (axisCount n)) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (c:UniformLocalCacheSlotHeaderMachine.Parameters) (M:ℕ) : ℕ :=
 max (max M c.ambient)
  (DFTModelCacheMatchingProduced.mixedPeakBudget c.ambient (radix n j)
   (UniformMasterRootMachine.order n) (DFTModelCacheRectangleMetadata.kernel n j q original)
   (DFTModelCacheRectanglePreparation.height q) M)

theorem ambient_native {B:ℕ} (n:ℕ) (hn:0<n) (j:Fin (axisCount n)) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (c:UniformLocalCacheSlotHeaderMachine.Parameters)
 (slot:UniformLocalCacheChronology.Slot)
 (source:DFTModelCacheRectanglePreparation.ProducedRow (radix n j) q)
 (extent:q.offset+q.width≤c.ambient)
 (layout:UniformChunkMatchingPreparation.Layout (DFTModelCacheRectangleMetadata.chunk q original c slot) B)
 (positive:original.C+UniformToeplitzCrossDAG.bankSize (DFTModelCacheRectanglePreparation.height q)≤original.negative)
 (negative:original.negative+UniformToeplitzCrossDAG.bankSize (DFTModelCacheRectanglePreparation.height q)≤original.constants) :
 let p:=DFTModelCacheRectangleMetadata.chunk q original c slot
 let ha: p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height :=
  (DFTModelCacheRectangleMetadata.chunk_widths source original c slot).1
 let he: p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height :=
  (DFTModelCacheRectangleMetadata.chunk_widths source original c slot).2
 let W:=UniformChunkMatchingPreparation.crossWord p ha he
 let E:=UniformChunkMatchingPreparation.physicalEdges layout W
  (UniformChunkMatchingPreparation.cross_domain p ha he)
 let raw:=(DFTModelCacheDisplacement.metadata (radix n j)
  (DFTModelCacheRectangleMetadata.kernel n j q original),
  (UniformMasterRootMachine.order n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)))
 let x:=DFTModelCacheAmbientPool.args q.offset c.ambient p.height.K
  original.C original.negative original.constants raw
  (mappedRows p layout ha he original.C original.negative original.constants)
 let bank:=UniformToeplitzCrossDAG.sharedBank (DFTModelCacheRectanglePreparation.height q)
  (UniformRankCrossPreparationMachine.kernelValues
   (UniformSeedHeightPreparation.parameters n j (DFTModelCacheRectangleMetadata.actual q original)).base
   (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j))
 (run DFTModelCacheAmbientPool.program x).valid ∧
 (run DFTModelCacheAmbientPool.program x).work≤ambientWorkBudget n j q original c (UniformChunkMatchingPreparation.indices p W).length ∧
 (run DFTModelCacheAmbientPool.program x).peak≤ambientPeakBudget n j q original c (UniformChunkMatchingPreparation.indices p W).length ∧
 (run DFTModelCacheAmbientPool.program x).val.2.2.len=9*c.ambient ∧
 ∀lane:Fin 9,∀d:Fin c.ambient,
 (run DFTModelCacheAmbientPool.program x).val.2.2.look (lane.val*c.ambient+d.val) 0=
 UniformGlobalMatchingScaleBankBridge.nativeFactor
  (fun i=>UniformTranslatedMatchingRows.edge q.offset (E i))
  (fun i=>UniformMatchingConjugateLoadMachine.value (DFTModelCacheRectanglePreparation.height q) bank
   (UniformPackedMatchingShearMachine.selectedLabels p W i.val)) lane d.val := by
 dsimp only
 let p:=DFTModelCacheRectangleMetadata.chunk q original c slot
 have widths:=DFTModelCacheRectangleMetadata.chunk_widths source original c slot
 let W:=UniformChunkMatchingPreparation.crossWord p widths.1 widths.2
 let domain:=UniformChunkMatchingPreparation.cross_domain p widths.1 widths.2
 let rs:=mappedRows p layout widths.1 widths.2 original.C original.negative original.constants
 have matching:=DFTModelCacheSelectedPhysicalRows.native_matching p layout W
  original.C original.negative original.constants domain
  (UniformChunkMatchingPreparation.cross_degree p widths.1 widths.2)
 have labels:=DFTModelCacheSelectedPhysicalRows.native_source p layout.capacity W
  original.C original.negative original.constants domain
 obtain ⟨hD,hr,hN,h4⟩:=DFTModelCacheRectangleMetadata.selected_divisors n hn j q source
 have ambient:=DFTModelCacheAmbientPool.specification q.offset q.width c.ambient
  (radix n j) (UniformMasterRootMachine.order n)
  (DFTModelCacheRectangleMetadata.kernel n j q original)
  (DFTModelCacheRectangleMetadata.kernel_shape n j q original source)
  p.height.K original.C original.negative original.constants rfl hD hr hN h4 rs _
  matching.1 matching.2.1 matching.2.2 extent (by
   have two:=layout.radixPositive
   change 2≤q.width at two
   omega)
  (fun i=>UniformPackedMatchingShearMachine.selectedLabels p W i.val)
  labels positive negative
 refine ⟨ambient.1,ambient.2.1,ambient.2.2.1,ambient.2.2.2.2.1,?_⟩
 intro lane d
 have factors:=ambient.2.2.2.2.2 lane d
 have hb:DFTModelCacheSpectrum.rankKernels (radix n j)
  (DFTModelCacheRectangleMetadata.kernel n j q original) p.height.K (OAI.ExactFourier.zeta (radix n j))=
  UniformRankCrossPreparationMachine.kernelValues
   (UniformSeedHeightPreparation.parameters n j (DFTModelCacheRectangleMetadata.actual q original)).base
   (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j):=
  DFTModelCacheRectangleMetadata.rankKernels_eq n j q original
 rw [hb] at factors
 exact factors


end
end ExactFourierCircuits.DFTModelCacheRectangleAmbientCaller

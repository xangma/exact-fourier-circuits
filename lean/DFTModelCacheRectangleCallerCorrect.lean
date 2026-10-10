import DFTModelCacheRectangleCallerExecution

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheRectangleCaller
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalRectangleDescriptors UniformAllAxisSeedPreparation
noncomputable section
attribute [local irreducible] Code.run program DFTModelCacheSelectedPhysicalRowsCaller.program

def workBudget (n:ℕ) (j:Fin (axisCount n)) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (c:UniformLocalCacheSlotHeaderMachine.Parameters)
 (slot:UniformLocalCacheChronology.Slot) (M:ℕ) : ℕ :=
 28*DFTModelCacheRectanglePreparation.height q+35+
 DFTModelCacheSelectedPhysicalRowsCaller.mixedWorkBudget
  (DFTModelCacheRectangleMetadata.chunk q original c slot) (radix n j)
  (UniformMasterRootMachine.order n) (DFTModelCacheRectangleMetadata.kernel n j q original) M+291

/-- One genuine descriptor supplies the geometry, kernel metadata and slot;
the selected axis supplies the master and the original H/G root order. The
charged program generates topology, rows, colors, borrowed locations,
coefficient labels, permutation and local factors internally. Physical
translation by q.offset and ambient expansion are a separate later stage. -/
theorem specification {B:ℕ} (n:ℕ) (hn:0<n) (j:Fin (axisCount n)) (q:Row)
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
 let domain:=UniformChunkMatchingPreparation.cross_domain p ha he
 let E:=UniformChunkMatchingPreparation.physicalEdges layout W domain
 let bank:=UniformToeplitzCrossDAG.sharedBank (DFTModelCacheRectanglePreparation.height q)
  (UniformRankCrossPreparationMachine.kernelValues
   (UniformSeedHeightPreparation.parameters n j (DFTModelCacheRectangleMetadata.actual q original)).base
   (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j))
 let x:=genuineInput n j q original slot
 ∃u ticks,DFTModelCacheTopology.Result q.a q.e u ticks ∧
 (run program x).valid ∧
 (run program x).work≤workBudget n j q original c slot (UniformChunkMatchingPreparation.indices p W).length ∧
 (run program x).val.1=(x,preparedConfig q) ∧
 (run program x).val.2.2.2.len=9*q.width ∧
 ∀lane:Fin 9,∀d:Fin q.width,
 (run program x).val.2.2.2.look (lane.val*q.width+d.val) 0=
 UniformGlobalMatchingScaleBankBridge.nativeFactor E
  (fun i=>UniformMatchingConjugateLoadMachine.value (DFTModelCacheRectanglePreparation.height q) bank
   (UniformPackedMatchingShearMachine.selectedLabels p W i.val)) lane d.val := by
 dsimp only
 let p:=DFTModelCacheRectangleMetadata.chunk q original c slot
 have widths:=DFTModelCacheRectangleMetadata.chunk_widths source original c slot
 obtain ⟨hD,hr,hN,h4⟩:=DFTModelCacheRectangleMetadata.selected_divisors n hn j q source
 obtain ⟨u,ticks,result,valid,work,_,len,factors⟩:=
  DFTModelCacheSelectedPhysicalRowsCaller.mixed_specification p layout
   (DFTModelCacheRectangleMetadata.chunk_computed q original c slot) widths.1 widths.2 height
   (radix n j) (UniformMasterRootMachine.order n) (DFTModelCacheRectangleMetadata.kernel n j q original)
   (DFTModelCacheRectangleMetadata.kernel_shape n j q original source) rfl
   hD hr hN h4 original.C original.negative original.constants positive negative
 refine ⟨u,ticks,result,(genuine_valid n j q original c slot).2 valid,?_,?_,?_,?_⟩
 · rw [genuine_work n j q original c slot]
   exact Nat.add_le_add_right (Nat.add_le_add_left work (28*DFTModelCacheRectanglePreparation.height q+35)) 291
 · rw [genuine_value n j q original c slot]
 · rw [genuine_value n j q original c slot]
   exact len
 · intro lane d
   rw [genuine_value n j q original c slot]
   have hb:DFTModelCacheSpectrum.rankKernels (radix n j)
    (DFTModelCacheRectangleMetadata.kernel n j q original) p.height.K (OAI.ExactFourier.zeta (radix n j))=
    UniformRankCrossPreparationMachine.kernelValues
     (UniformSeedHeightPreparation.parameters n j (DFTModelCacheRectangleMetadata.actual q original)).base
     (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j):=
    DFTModelCacheRectangleMetadata.rankKernels_eq n j q original
   have hf:=factors lane d
   rw [hb] at hf
   exact hf

end
end ExactFourierCircuits.DFTModelCacheRectangleCaller

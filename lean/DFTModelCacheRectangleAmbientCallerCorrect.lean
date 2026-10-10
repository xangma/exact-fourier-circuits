import DFTModelCacheRectangleAmbientCallerSource
import DFTModelCacheRectangleAmbientCallerProvenance

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheRectangleAmbientCaller
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalRectangleDescriptors UniformAllAxisSeedPreparation
noncomputable section
attribute [local irreducible] Code.run program DFTModelCacheRectangleCaller.program
 DFTModelCacheAmbientPool.program

def workBudget (n:ℕ) (j:Fin (axisCount n)) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (c:UniformLocalCacheSlotHeaderMachine.Parameters)
 (slot:UniformLocalCacheChronology.Slot) (M:ℕ) : ℕ :=
 DFTModelCacheRectangleCaller.workBudget n j q original c slot M+
 ambientWorkBudget n j q original c M+83

def peakBudget (n:ℕ) (j:Fin (axisCount n)) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (c:UniformLocalCacheSlotHeaderMachine.Parameters)
 (slot:UniformLocalCacheChronology.Slot) (M:ℕ) : ℕ :=
 max (DFTModelCacheRectangleCaller.peakBudget n j q original c slot M)
  (max 1 (ambientPeakBudget n j q original c M))

theorem first_bounds {B:ℕ} (n:ℕ) (hn:0<n) (j:Fin (axisCount n)) (q:Row)
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
 let x:=genuineInput c.ambient n j q original slot
 (run DFTModelCacheRectangleCaller.program x.2).valid ∧
 (run DFTModelCacheRectangleCaller.program x.2).work≤DFTModelCacheRectangleCaller.workBudget n j q original c slot (UniformChunkMatchingPreparation.indices p W).length ∧
 (run DFTModelCacheRectangleCaller.program x.2).peak≤DFTModelCacheRectangleCaller.peakBudget n j q original c slot (UniformChunkMatchingPreparation.indices p W).length := by
 dsimp only
 obtain ⟨u,ticks,result,valid,work,_,_,_⟩:=DFTModelCacheRectangleCaller.specification
  n hn j q original c slot source layout height positive negative
 have peak:=DFTModelCacheRectangleCaller.peak n hn j q original c slot source layout height positive negative
 exact ⟨valid,work,peak⟩

theorem generated_ambient {B:ℕ} (n:ℕ) (hn:0<n) (j:Fin (axisCount n)) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (c:UniformLocalCacheSlotHeaderMachine.Parameters)
 (slot:UniformLocalCacheChronology.Slot)
 (source:DFTModelCacheRectanglePreparation.ProducedRow (radix n j) q)
 (extent:q.offset+q.width≤c.ambient)
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
 let E:=UniformChunkMatchingPreparation.physicalEdges layout W
  (UniformChunkMatchingPreparation.cross_domain p ha he)
 let x:=argumentValue (c.ambient,(run DFTModelCacheRectangleCaller.program
  (DFTModelCacheRectangleCaller.genuineInput n j q original slot)).val)
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
 rw [argument_native c.ambient n j q original c slot source layout (by
  exact height)]
 exact ambient_native n hn j q original c slot source extent layout positive negative

/-- A rooted descriptor and the genuine selected axis determine all local
rows, colors, labels, roots, spectra, permutations and both factor pools.
Only ordinary native layout, slot-height and address separation remain. -/
theorem produced_specification {B:ℕ} (n:ℕ) (hn:0<n) (j:Fin (axisCount n)) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (c:UniformLocalCacheSlotHeaderMachine.Parameters)
 (slot:UniformLocalCacheChronology.Slot)
 (source:DFTModelCacheRectanglePreparation.ProducedRow (radix n j) q)
 (extent:q.offset+q.width≤c.ambient)
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
 let E:=UniformChunkMatchingPreparation.physicalEdges layout W
  (UniformChunkMatchingPreparation.cross_domain p ha he)
 let bank:=UniformToeplitzCrossDAG.sharedBank (DFTModelCacheRectanglePreparation.height q)
  (UniformRankCrossPreparationMachine.kernelValues
   (UniformSeedHeightPreparation.parameters n j (DFTModelCacheRectangleMetadata.actual q original)).base
   (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j))
 let x:=genuineInput c.ambient n j q original slot
 (run program x).valid ∧
 (run program x).work≤workBudget n j q original c slot (UniformChunkMatchingPreparation.indices p W).length ∧
 (run program x).peak≤peakBudget n j q original c slot (UniformChunkMatchingPreparation.indices p W).length ∧
 (run program x).val.1=(c.ambient,(run DFTModelCacheRectangleCaller.program x.2).val) ∧
 (run program x).val.2.2.2.len=9*c.ambient ∧
 ∀lane:Fin 9,∀d:Fin c.ambient,
 (run program x).val.2.2.2.look (lane.val*c.ambient+d.val) 0=
 UniformGlobalMatchingScaleBankBridge.nativeFactor
  (fun i=>UniformTranslatedMatchingRows.edge q.offset (E i))
  (fun i=>UniformMatchingConjugateLoadMachine.value (DFTModelCacheRectanglePreparation.height q) bank
   (UniformPackedMatchingShearMachine.selectedLabels p W i.val)) lane d.val := by
 dsimp only
 have first:=first_bounds n hn j q original c slot source layout height positive negative
 have second:=generated_ambient n hn j q original c slot source extent layout height positive negative
 let p:=DFTModelCacheRectangleMetadata.chunk q original c slot
 have widths:=DFTModelCacheRectangleMetadata.chunk_widths source original c slot
 let W:=UniformChunkMatchingPreparation.crossWord p widths.1 widths.2
 let E:=UniformChunkMatchingPreparation.physicalEdges layout W
  (UniformChunkMatchingPreparation.cross_domain p widths.1 widths.2)
 let bank:=UniformToeplitzCrossDAG.sharedBank (DFTModelCacheRectanglePreparation.height q)
  (UniformRankCrossPreparationMachine.kernelValues
   (UniformSeedHeightPreparation.parameters n j (DFTModelCacheRectangleMetadata.actual q original)).base
   (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j))
 exact composition (property:=fun output=>output.2.2.len=9*c.ambient ∧
  ∀lane:Fin 9,∀d:Fin c.ambient,output.2.2.look (lane.val*c.ambient+d.val) 0=
   UniformGlobalMatchingScaleBankBridge.nativeFactor
    (fun i=>UniformTranslatedMatchingRows.edge q.offset (E i))
    (fun i=>UniformMatchingConjugateLoadMachine.value (DFTModelCacheRectanglePreparation.height q) bank
     (UniformPackedMatchingShearMachine.selectedLabels p W i.val)) lane d.val)
  rfl first ⟨second.1,second.2.1,second.2.2.1,second.2.2.2⟩

/-- A rooted descriptor and the genuine selected axis determine all local
rows, colors, labels, roots, spectra, permutations and both factor pools.
Only ordinary native layout, slot-height and address separation remain. -/
theorem specification {B:ℕ} (n:ℕ) (hn:0<n) (j:Fin (axisCount n)) (q:Row)
 (original:UniformSeedHeightPreparation.Config) (c:UniformLocalCacheSlotHeaderMachine.Parameters)
 (slot:UniformLocalCacheChronology.Slot)
 (member:q∈(UniformLocalCacheTreeMachine.ofPlan
  (UniformBalancedToeplitz.plan (radix n j)) 0).rectangles)
 (ambientBound:radix n j≤c.ambient)
 (layout:UniformChunkMatchingPreparation.Layout (DFTModelCacheRectangleMetadata.chunk q original c slot) B)
 (height:slot.depth≤8*DFTModelCacheRectanglePreparation.height q+6)
 (positive:original.C+UniformToeplitzCrossDAG.bankSize (DFTModelCacheRectanglePreparation.height q)≤original.negative)
 (negative:original.negative+UniformToeplitzCrossDAG.bankSize (DFTModelCacheRectanglePreparation.height q)≤original.constants) :
 let source:DFTModelCacheRectanglePreparation.ProducedRow (radix n j) q:=
  (rooted_source (radix n j) c.ambient q member ambientBound).1
 let p:=DFTModelCacheRectangleMetadata.chunk q original c slot
 let ha: p.height.a≤UniformCrossHeightPreparationMachine.widthOf p.height :=
  (DFTModelCacheRectangleMetadata.chunk_widths source original c slot).1
 let he: p.height.e≤UniformCrossHeightPreparationMachine.widthOf p.height :=
  (DFTModelCacheRectangleMetadata.chunk_widths source original c slot).2
 let W:=UniformChunkMatchingPreparation.crossWord p ha he
 let E:=UniformChunkMatchingPreparation.physicalEdges layout W
  (UniformChunkMatchingPreparation.cross_domain p ha he)
 let bank:=UniformToeplitzCrossDAG.sharedBank (DFTModelCacheRectanglePreparation.height q)
  (UniformRankCrossPreparationMachine.kernelValues
   (UniformSeedHeightPreparation.parameters n j (DFTModelCacheRectangleMetadata.actual q original)).base
   (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j))
 let x:=genuineInput c.ambient n j q original slot
 (run program x).valid ∧
 (run program x).work≤workBudget n j q original c slot (UniformChunkMatchingPreparation.indices p W).length ∧
 (run program x).peak≤peakBudget n j q original c slot (UniformChunkMatchingPreparation.indices p W).length ∧
 (run program x).val.1=(c.ambient,(run DFTModelCacheRectangleCaller.program x.2).val) ∧
 (run program x).val.2.2.2.len=9*c.ambient ∧
 ∀lane:Fin 9,∀d:Fin c.ambient,
 (run program x).val.2.2.2.look (lane.val*c.ambient+d.val) 0=
 UniformGlobalMatchingScaleBankBridge.nativeFactor
  (fun i=>UniformTranslatedMatchingRows.edge q.offset (E i))
  (fun i=>UniformMatchingConjugateLoadMachine.value (DFTModelCacheRectanglePreparation.height q) bank
   (UniformPackedMatchingShearMachine.selectedLabels p W i.val)) lane d.val := by
 exact produced_specification n hn j q original c slot
  (rooted_source (radix n j) c.ambient q member ambientBound).1
  (rooted_source (radix n j) c.ambient q member ambientBound).2
  layout height positive negative

end
end ExactFourierCircuits.DFTModelCacheRectangleAmbientCaller

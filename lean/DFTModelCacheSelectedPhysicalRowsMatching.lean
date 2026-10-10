import DFTModelCacheSelectedPhysicalRowsPeak
import DFTModelCacheMatchingProducedCorrect

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheSelectedPhysicalRows
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheColor (Row)
open DFTModelCacheSelectedCoefficients (physicalRows_lookup)
noncomputable section
attribute [local irreducible] program

/-- The actual mapped producer supplies the physical matching endpoints. No
physical row-range certificate or decoded coefficient list is an input. -/
theorem native_rows {R B:ℕ} (p:UniformChunkMatchingPreparation.Parameters)
 (layout:UniformChunkMatchingPreparation.Layout p B)
 (W:List (UniformReplayPrint.ShearCode ℕ R)) (C T P:ℕ)
 (domain:UniformChunkMatchingPreparation.CodesDomain p W) :
 DFTModelCacheMatchingNat.Rows (UniformChunkMatchingPreparation.physicalEdges layout W domain)
  (run program (chunkGeometry p,rowTape (UniformChunkMatchingPreparation.selectedRows p W
   (UniformCrossShearTableMachine.locations R C T P)))).val := by
 rw [native_value p layout.capacity W C T P domain]
 have len:=UniformPackedMatchingShearMachine.mappedRows_length p layout.capacity W
  (UniformCrossShearTableMachine.locations R C T P)
 refine ⟨len,?_⟩
 intro i
 have hi:i.val<(UniformChunkMatchingPreparation.mappedRows p layout.capacity W
  (UniformCrossShearTableMachine.locations R C T P)).length:=len.symm ▸ i.isLt
 change ((DFTModelCacheSelectedCoefficients.physicalRows _).look i.val Row.blank).1=_ ∧
  ((DFTModelCacheSelectedCoefficients.physicalRows _).look i.val Row.blank).2.1=_
 rw [physicalRows_lookup _ ⟨i.val,hi⟩]
 have align:=UniformChunkMatchingPreparation.selected_align p W
  (UniformCrossShearTableMachine.locations R C T P) i
 simp only [UniformChunkMatchingPreparation.mappedRows,List.getElem_map,
  UniformChunkRowTableMachine.mappedRow,UniformChunkRowTableMachine.borrowed,
  UniformChunkMatchingPreparation.rowParameters,UniformChunkMatchingPreparation.physicalEdges]
 exact ⟨congrArg (UniformChunkMatchingPreparation.coordinate p layout.capacity) align.1,
  congrArg (UniformChunkMatchingPreparation.coordinate p layout.capacity) align.2⟩

theorem native_matching {R B:ℕ} (p:UniformChunkMatchingPreparation.Parameters)
 (layout:UniformChunkMatchingPreparation.Layout p B)
 (W:List (UniformReplayPrint.ShearCode ℕ R)) (C T P:ℕ)
 (domain:UniformChunkMatchingPreparation.CodesDomain p W)
 (degree:UniformColoring.DegreeBound (UniformChunkMatchingPreparation.edges W) 6) :
 DFTModelCacheMatchingNat.Rows (UniformChunkMatchingPreparation.physicalEdges layout W domain)
  (run program (chunkGeometry p,rowTape (UniformChunkMatchingPreparation.selectedRows p W
   (UniformCrossShearTableMachine.locations R C T P)))).val ∧
 UniformMatchingAxisTableMachine.Matching (UniformChunkMatchingPreparation.physicalEdges layout W domain) ∧
 UniformMatchingAxisTableMachine.InRange p.radix (UniformChunkMatchingPreparation.physicalEdges layout W domain) :=
 ⟨native_rows p layout W C T P domain,
  UniformChunkMatchingPreparation.physical_matching layout domain degree,
  UniformChunkMatchingPreparation.physical_range layout domain⟩

end
end ExactFourierCircuits.DFTModelCacheSelectedPhysicalRows

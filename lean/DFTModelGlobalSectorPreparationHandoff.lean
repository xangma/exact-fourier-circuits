import DFTModelGlobalSectorPreparationSpecification
import DFTModelSectorMapPeak

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheTraversal
noncomputable section

/-- This directory is computed by the charged producer, not supplied by the caller. -/
def generatedDirectory (as : List UniformSectorPacking.Axis) : Directory.T :=
 (run withDirectory (ofList (as.map encodeAxis))).val.2

theorem generated_directory (as : List UniformSectorPacking.Axis) :
 generatedDirectory as=((UniformSectorPacking.radices as).prod,
   ofList ((UniformSectorPacking.sectorStates as).map (fun s=>(s.start,s.width)))) :=
 (withDirectory_value as).2

theorem generated_encoded (as : List UniformSectorPacking.Axis) :
 DFTModelSectorMap.Encoded (UniformSectorPacking.sectorStates as) (generatedDirectory as).2 := by
 rw [generated_directory]
 refine ⟨by simp [ofList],?_⟩
 intro i hi
 simp [ofList_look,hi]

theorem generated_geometry (as : List UniformSectorPacking.Axis) :
 DFTModelSectorMap.Geometry (generatedDirectory as).1 (generatedDirectory as).2 := by
 have h:=DFTModelSectorMap.canonical_geometry as _ (generated_encoded as)
 simpa only [generated_directory] using h

theorem generated_count (as : List UniformSectorPacking.Axis) :
 (generatedDirectory as).2.len≤(generatedDirectory as).1 := by
 have h:=DFTModelSectorMap.canonical_count as _ (generated_encoded as)
 simpa only [generated_directory] using h

theorem generated_positive (as : List UniformSectorPacking.Axis) (i : ℕ)
 (hi:i<(generatedDirectory as).2.len) :
 0<((generatedDirectory as).2.look i (0,0)).2 :=
 DFTModelSectorMap.canonical_positive as _ (generated_encoded as) i hi

/-- The actual map program's geometry and count are discharged by the generated rows. -/
theorem generated_map_specification (as : List UniformSectorPacking.Axis) :
 (run DFTModelSectorMap.program (generatedDirectory as)).valid ∧
 (run DFTModelSectorMap.program (generatedDirectory as)).val.len=(generatedDirectory as).1 ∧
 (run DFTModelSectorMap.program (generatedDirectory as)).work≤2000*((generatedDirectory as).1+1) ∧
 (run DFTModelSectorMap.program (generatedDirectory as)).peak≤6*((generatedDirectory as).1+1) :=
 DFTModelSectorMap.specification (generated_geometry as) (generated_count as)

/-- Generated saving-child metadata has genuine power-of-two width and fitted start. -/
theorem generated_sector_shape (as : List UniformSectorPacking.Axis) (i : ℕ)
 (hi:i<(UniformSectorPacking.sectorStates as).length) :
 let u:=(run program (ofList (as.map encodeAxis))).val
 let row:=u.2.2.2.look i (0,(0,0))
 row.2.1=2^row.1 ∧ row.1≤as.length ∧ row.2.2+row.2.1≤u.1 := by
 have source:=program_native as
 dsimp only at source
 dsimp only
 rw [source.2.2.2.2.2]
 have look:(ofList ((UniformSectorPacking.sectorStates as).map encodeSector)).look i (0,(0,0))=
     encodeSector ((UniformSectorPacking.sectorStates as)[i]'hi) := by
   simp [ofList_look,hi]
 rw [look]
 have width:=UniformSectorBatchDirectoryMachine.sector_width as i hi
 have fit:=UniformSectorBatchDirectoryMachine.sector_fits as i hi
 have count:((UniformSectorPacking.sectorStates as)[i]'hi).pairs≤as.length := by
   simp only [UniformSectorPacking.sectorStates,List.getElem_ofFn,
     UniformSectorPacking.expectedBlockState]
   exact UniformSectorPacking.sectorPairCount_le as _
 change _=2^_ ∧ _≤as.length ∧ _+_≤_
 exact ⟨width,count,by rw [source.1];exact fit⟩

end
end ExactFourierCircuits.DFTModelGlobalSectorPreparation

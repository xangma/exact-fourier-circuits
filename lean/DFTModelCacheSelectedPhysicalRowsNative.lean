import DFTModelCacheSelectedPhysicalRowsValues

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheSelectedPhysicalRows
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheColor (Row)
open DFTModelCacheColorSelection (comp_value fork_value)
open DFTModelCacheSelectedCoefficients (tab_lookup physicalRows_lookup)
noncomputable section
attribute [local irreducible] borrowed coordinate

def rowGeometry (p:UniformChunkRowTableMachine.Parameters) : Geometry.T :=
 geom p.v p.source p.e p.target p.a p.g

theorem prepare_value (x:Input.T) :
 (run prepare x).val=(x,(run borrowed x.1).val) := by
 rw [prepare,fork_value,comp_value]
 rfl

theorem mapRow_value (p:UniformChunkRowTableMachine.Parameters) (fit:p.g+p.e+p.a≤p.v)
 (qs:List UniformInPlaceMachine.Row) (domain:UniformChunkRowTableMachine.RowsDomain p qs)
 (j:ℕ) (hj:j<qs.length) :
 (run mapRow (((rowGeometry p,rowTape qs),(run borrowed (rowGeometry p)).val),j)).val=
 encode (UniformChunkRowTableMachine.mappedRow p fit qs[j]) := by
 have lookup:(rowTape qs).look j Row.blank=encode qs[j]:=physicalRows_lookup qs ⟨j,hj⟩
 have ports:=domain qs[j] (List.getElem_mem hj)
 rw [mapRow,fork_value,fork_value]
 change ((run coordinate (((rowGeometry p,rowTape qs),(run borrowed (rowGeometry p)).val),
  ((rowTape qs).look j Row.blank).1)).val,
  ((run coordinate (((rowGeometry p,rowTape qs),(run borrowed (rowGeometry p)).val),
   ((rowTape qs).look j Row.blank).2.1)).val,((rowTape qs).look j Row.blank).2.2))=_
 rw [lookup]
 simp only [rowGeometry,encode]
 rw [coordinate_value p.v p.source p.e p.target p.a p.g qs[j].dst (rowTape qs) fit ports.1,
  coordinate_value p.v p.source p.e p.target p.a p.g qs[j].src (rowTape qs) fit ports.2]
 rfl

theorem mapper_value (p:UniformChunkRowTableMachine.Parameters) (fit:p.g+p.e+p.a≤p.v)
 (qs:List UniformInPlaceMachine.Row) (domain:UniformChunkRowTableMachine.RowsDomain p qs) :
 (run mapper ((rowGeometry p,rowTape qs),(run borrowed (rowGeometry p)).val)).val=
 rowTape (qs.map (UniformChunkRowTableMachine.mappedRow p fit)) := by
 rw [mapper,DFTModelCacheMatchingNat.tab_value_code]
 change Tape.tab qs.length (fun j=>(run mapRow
  (((rowGeometry p,rowTape qs),(run borrowed (rowGeometry p)).val),j)).val)=_
 apply DFTModelCacheTraversal.tape_ext _ _ Row.blank
 · simp only [rowTape,DFTModelCacheSelectedCoefficients.physicalRows,Tape.tab,List.length_map]
 · intro j hj
   change j<qs.length at hj
   rw [tab_lookup _ _ j Row.blank hj,mapRow_value p fit qs domain j hj]
   change encode (UniformChunkRowTableMachine.mappedRow p fit qs[j])=
    (DFTModelCacheSelectedCoefficients.physicalRows (qs.map (UniformChunkRowTableMachine.mappedRow p fit))).look j Row.blank
   rw [physicalRows_lookup _ ⟨j,by simpa only [List.length_map] using hj⟩]
   simp only [List.getElem_map]
   rfl

/-- Native59 row values with the exact Borrowed17 injection. Only ordinary fit
and genuine replay-port domain are required; no physical range is supplied. -/
theorem program_value (p:UniformChunkRowTableMachine.Parameters) (fit:p.g+p.e+p.a≤p.v)
 (qs:List UniformInPlaceMachine.Row) (domain:UniformChunkRowTableMachine.RowsDomain p qs) :
 (run program (rowGeometry p,rowTape qs)).val=
 rowTape (qs.map (UniformChunkRowTableMachine.mappedRow p fit)) := by
 rw [program,comp_value,prepare_value]
 exact mapper_value p fit qs domain

def chunkGeometry (p:UniformChunkMatchingPreparation.Parameters) : Geometry.T :=
 rowGeometry (UniformChunkMatchingPreparation.rowParameters p)

theorem native_value {R:ℕ} (p:UniformChunkMatchingPreparation.Parameters)
 (fit:UniformCrossHeightPreparationMachine.gates p.height+p.height.e+p.height.a≤p.radix)
 (W:List (UniformReplayPrint.ShearCode ℕ R)) (C T P:ℕ)
 (domain:UniformChunkMatchingPreparation.CodesDomain p W) :
 (run program (chunkGeometry p,rowTape (UniformChunkMatchingPreparation.selectedRows p W
  (UniformCrossShearTableMachine.locations R C T P)))).val=
 rowTape (UniformChunkMatchingPreparation.mappedRows p fit W
  (UniformCrossShearTableMachine.locations R C T P)) :=
 program_value (UniformChunkMatchingPreparation.rowParameters p) fit _
  (UniformChunkMatchingPreparation.selected_rows_domain _ domain)

/-- The computed physical rows carry exactly the native selected coefficient
labels, including repeated occurrences and zero or large physical addresses. -/
theorem native_source {R:ℕ} (p:UniformChunkMatchingPreparation.Parameters)
 (fit:UniformCrossHeightPreparationMachine.gates p.height+p.height.e+p.height.a≤p.radix)
 (W:List (UniformReplayPrint.ShearCode ℕ R)) (C T P:ℕ)
 (domain:UniformChunkMatchingPreparation.CodesDomain p W) :
 DFTModelCacheSelectedCoefficients.RowSource C T P
  (run program (chunkGeometry p,rowTape (UniformChunkMatchingPreparation.selectedRows p W
   (UniformCrossShearTableMachine.locations R C T P)))).val
  (fun i:Fin (UniformChunkMatchingPreparation.indices p W).length=>
   UniformPackedMatchingShearMachine.selectedLabels p W i.val) := by
 rw [native_value p fit W C T P domain]
 exact DFTModelCacheSelectedCoefficients.mapped_rows_source p fit W C T P

end
end ExactFourierCircuits.DFTModelCacheSelectedPhysicalRows

import DFTModelGlobalSectorPreparationDirectory
import DFTModelGlobalSectorPreparationPeakClosed

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheTraversal
noncomputable section
attribute [local irreducible] program tables finalize directory withDirectory

def localBudget (as : List UniformSectorPacking.Axis) : ℕ :=
 (as.map (fun a=>(a.widths.sum+1)^2)).sum

theorem native_work (as : List UniformSectorPacking.Axis) :
 (run program (ofList (as.map encodeAxis))).work≤
 5000*((UniformSectorPacking.radices as).prod+as.length+localBudget as+1) := by
 have h:=program_work (as.map encodeAxis) (by
   intro x hx
   obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hx
   exact native_blocks_bound a) (by
   intro x hx
   obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hx
   exact a.radix_two)
 simpa [volume,localWork,localBudget,encodeAxis,List.map_map,Function.comp_def] using h

/-- One actual closed producer; the honest local quadratic preparation remains separate. -/
theorem specification (as : List UniformSectorPacking.Axis) :
 (run program (ofList (as.map encodeAxis))).valid ∧
 (run program (ofList (as.map encodeAxis))).work≤
   5000*((UniformSectorPacking.radices as).prod+as.length+localBudget as+1) ∧
 (run program (ofList (as.map encodeAxis))).peak≤
   6*(UniformSectorPacking.radices as).prod+as.length+1 :=
 ⟨program_valid _,native_work as,program_peak as⟩

theorem withDirectory_work (as : List UniformSectorPacking.Axis) :
 (run withDirectory (ofList (as.map encodeAxis))).work≤
 6000*((UniformSectorPacking.radices as).prod+as.length+localBudget as+1) := by
 have hw:=native_work as
 have hg:=(native_tables_bound as).blocks
 have hc: (run program (ofList (as.map encodeAxis))).val.2.2.2.len≤
     (UniformSectorPacking.radices as).prod := by
   rw [program_value,tableValue_ofList,listTables_native]
   exact hg
 simp only [withDirectory,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
 change (run program (ofList (as.map encodeAxis))).work+
   (1+(run directory (run program (ofList (as.map encodeAxis))).val).work+1)+1≤_
 rw [directory_work]
 omega

theorem withDirectory_peak (as : List UniformSectorPacking.Axis) :
 (run withDirectory (ofList (as.map encodeAxis))).peak≤
   6*(UniformSectorPacking.radices as).prod+as.length+1 := by
 have hp:=program_peak as
 have hg:=(native_tables_bound as).blocks
 have hc: (run program (ofList (as.map encodeAxis))).val.2.2.2.len≤
     (UniformSectorPacking.radices as).prod := by
   rw [program_value,tableValue_ofList,listTables_native]
   exact hg
 simp only [withDirectory,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,max_zero]
 change max (run program (ofList (as.map encodeAxis))).peak
   (max 0 (run directory (run program (ofList (as.map encodeAxis))).val).peak)≤_
 rw [directory_peak]
 exact max_le hp (by omega)

end
end ExactFourierCircuits.DFTModelGlobalSectorPreparation

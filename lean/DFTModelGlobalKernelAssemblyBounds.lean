import DFTModelGlobalKernelAssemblyRun

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalKernelAssembly
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualBoolean DFTModelCacheTraversal
open scoped BigOperators
noncomputable section

def nativeInput (as:List UniformSectorPacking.Axis) (I:ℂ) (W:ℕ) (v:Tape Tagged.T) : Input.T :=
 (ofList (as.map DFTModelGlobalSectorPreparation.encodeAxis),(I,(W,v)))

theorem prepared_first (as:List UniformSectorPacking.Axis) (I:ℂ) (W:ℕ) (v:Tape Tagged.T) :
 (prepared (nativeInput as I W v)).1=
 (run DFTModelGlobalSectorPreparation.program
  (ofList (as.map DFTModelGlobalSectorPreparation.encodeAxis))).val :=
 (DFTModelGlobalSectorPreparation.withDirectory_value as).1

theorem prepared_directory (as:List UniformSectorPacking.Axis) (I:ℂ) (W:ℕ) (v:Tape Tagged.T) :
 (prepared (nativeInput as I W v)).2=DFTModelGlobalSectorPreparation.generatedDirectory as :=rfl

theorem prepared_volume (as:List UniformSectorPacking.Axis) (I:ℂ) (W:ℕ) (v:Tape Tagged.T) :
 (prepared (nativeInput as I W v)).1.1=(UniformSectorPacking.radices as).prod := by
 rw [prepared_first]
 exact (DFTModelGlobalSectorPreparation.program_native as).1

theorem prepared_consistent (as:List UniformSectorPacking.Axis) (I:ℂ) (W:ℕ) (v:Tape Tagged.T) :
 (prepared (nativeInput as I W v)).2.1=(prepared (nativeInput as I W v)).1.1 := by
 rw [prepared_directory,DFTModelGlobalSectorPreparation.generated_directory,prepared_volume]

theorem prepared_count (as:List UniformSectorPacking.Axis) (I:ℂ) (W:ℕ) (v:Tape Tagged.T) :
 (prepared (nativeInput as I W v)).1.2.2.2.len≤(prepared (nativeInput as I W v)).1.1 := by
 rw [prepared_first]
 have h:=DFTModelGlobalSectorPreparation.program_native as
 rw [h.2.2.2.2.2,h.1]
 simpa [ofList,DFTModelGlobalSectorPreparation.generated_directory] using
  DFTModelGlobalSectorPreparation.generated_count as

theorem program_valid (as:List UniformSectorPacking.Axis) (I:ℂ) (W:ℕ) (v:Tape Tagged.T) :
 (run program (nativeInput as I W v)).valid := by
 rw [program_run]
 simp only [Bill.pass,Bill.pay,retain_run,Bill.one]
 rw [preparation_value,gather_value,solve_value,merge_value]
 rw [preparation_run,gather_run,solve_run,merge_run,scatter_run]
 simp only [Bill.pay]
 simp only [DFTModelGlobalSectorPreparation.withDirectory_valid,true_and,and_true]
 refine ⟨move_valid _ _ _ _,sectors_valid _ _ _ _ _,?_,move_valid _ _ _ _⟩
 have g:=DFTModelGlobalSectorPreparation.generated_geometry as
 rw [←prepared_directory as I W v] at g
 exact DFTModelSectorMaterialization.joined_valid Tagged g _ _

theorem overlay_boolean (V j:ℕ) (m:Tape DFTModelSectorMap.Cell.T)
 (ps:Tape (Tape Tagged.T)) (v:Tape Tagged.T) (old:Boolean v)
 (children:∀i,Boolean (ps.look i (Tape.empty Tagged.T))) :
 (DFTModelSectorMap.overlay V j m ps v Tagged.blank).1<2 := by
 unfold DFTModelSectorMap.overlay
 dsimp only
 split
 · exact look_boolean old _
 · exact look_boolean (children _) _

theorem joined_boolean (W V:ℕ) (d:Tape (ℕ×ℕ))
 (ps:Tape (Tape Tagged.T)) (v:Tape Tagged.T) (old:Boolean v)
 (children:∀i,Boolean (ps.look i (Tape.empty Tagged.T))) :
 Boolean (run (DFTModelSectorMaterialization.joined Tagged) (W,((V,d),(ps,v)))).val.2 := by
 rw [DFTModelSectorMaterialization.joined_value,DFTModelSectorMaterialization.program_value]
 exact tab_boolean _ _ (fun j _=>overlay_boolean _ j _ _ _ old children)

theorem returned_boolean (x:Input.T) (before:Boolean x.2.2.2) : Boolean (returned x) := by
 have packedBool:Boolean (packed x):=by
  have h:=move_boolean x.2.2.1 (prepared x).1.1 (prepared x).1.2.2.1 x.2.2.2 before
  rw [move_value] at h
  exact h
 have patchBool:=patches_boolean x.2.1 x.2.2.1 (prepared x).1.1
  (prepared x).1.2.2.2 (packed x) packedBool
 have mergedBool:Boolean (materialized x).2:=joined_boolean _ _ _ _ _ packedBool patchBool
 have h:=move_boolean x.2.2.1 (prepared x).1.1 (prepared x).1.2.1 (materialized x).2 mergedBool
 rw [move_value] at h
 exact h

theorem program_boolean (x:Input.T) (before:Boolean x.2.2.2) : Boolean (run program x).val.2 := by
 rw [program_value]
 exact returned_boolean x before

theorem sectors_peak (I:ℂ) (W V:ℕ) (ss:Tape GP.Sector.T) (v:Tape Tagged.T) :
 (run sectors (I,(W,(V,(ss,v))))).peak=
 max ss.len ((Finset.range ss.len).sup
  (fun j=>(run DFTModelSectorTranspose.saving (sectorArgs I W V ss v j)).peak)) := by
 rw [sectors_run]
 change max (Bill.tab _ _ _).peak ss.len=_
 rw [ModelEquivalenceInterpreter.tab_peak]
 have h:(fun j=>(run sectorCell ((I,(W,(V,(ss,v)))),j)).peak)=
  fun j=>(run DFTModelSectorTranspose.saving (sectorArgs I W V ss v j)).peak := by
  funext j;rw [sectorCell_run];simp only [Bill.pay,Bill.pass,Bill.one,max_zero]
 rw [h]
 omega

theorem program_peak_stages (x:Input.T) :
 (run program x).peak=
 max (run DFTModelGlobalSectorPreparation.withDirectory x.1).peak
 (max (run move (x.2.2.1,((prepared x).1.1,((prepared x).1.2.2.1,x.2.2.2)))).peak
 (max (run sectors (x.2.1,(x.2.2.1,((prepared x).1.1,((prepared x).1.2.2.2,packed x))))).peak
 (max (run (DFTModelSectorMaterialization.joined Tagged)
   (x.2.2.1,((prepared x).2,(compactPatches x,packed x)))).peak
 (run move (x.2.2.1,((prepared x).1.1,((prepared x).1.2.1,(materialized x).2)))).peak))) := by
 rw [program_run]
 simp only [Bill.pass,Bill.pay,retain_run,Bill.one]
 rw [preparation_value,gather_value,solve_value,merge_value]
 rw [preparation_run,gather_run,solve_run,merge_run,scatter_run]
 simp only [Bill.pay,max_zero]
 rfl

end
end ExactFourierCircuits.DFTModelGlobalKernelAssembly

import DFTModelGlobalKernelAssemblySource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalKernelAssembly
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualBoolean DFTModelCacheTraversal
open scoped BigOperators
noncomputable section
attribute [local irreducible] UniformBatching.width DFTModelSavingPeak.wholeCoeff

def peakBudget (as:List UniformSectorPacking.Axis) : ℕ :=
 let V:=(UniformSectorPacking.radices as).prod
 max (6*V+as.length+1)
  (max (UniformBatching.width*V)
   (max (DFTModelSavingPeak.wholeCoeff*(V*V)) (6*(V+UniformBatching.width*V+1))))

theorem prepared_shape (as:List UniformSectorPacking.Axis) (I:ℂ) (W:ℕ) (v:Tape Tagged.T)
 (i:ℕ) (hi:i<(prepared (nativeInput as I W v)).1.2.2.2.len) :
 let p:=prepared (nativeInput as I W v)
 let row:=p.1.2.2.2.look i (0,(0,0))
 row.2.1=2^row.1 ∧row.1≤as.length ∧row.2.2+row.2.1≤p.1.1 := by
 dsimp only
 rw [prepared_first] at hi ⊢
 apply DFTModelGlobalSectorPreparation.generated_sector_shape as i
 rw [(DFTModelGlobalSectorPreparation.program_native as).2.2.2.2.2] at hi
 simpa [ofList] using hi

theorem program_peak (as:List UniformSectorPacking.Axis) (I:ℂ) (v:Tape Tagged.T)
 (before:Boolean v) :
 (run program (nativeInput as I UniformBatching.width v)).peak≤peakBudget as := by
 let x:=nativeInput as I UniformBatching.width v
 let V:=(UniformSectorPacking.radices as).prod
 have vol:(prepared x).1.1=V:=prepared_volume as I _ v
 have vb:V≤peakBudget as:=by unfold peakBudget;dsimp only [V];omega
 have wb:UniformBatching.width*V≤peakBudget as:=by unfold peakBudget;dsimp only [V];omega
 have cb:DFTModelSavingPeak.wholeCoeff*(V*V)≤peakBudget as:=by unfold peakBudget;dsimp only [V];omega
 have mb:6*(V+UniformBatching.width*V+1)≤peakBudget as:=by unfold peakBudget;dsimp only [V];omega
 have unpacked:∀j,j<(prepared x).1.1→(prepared x).1.2.2.1.look j 0<(prepared x).1.1:=by
  intro j hj
  rw [vol] at hj ⊢
  rw [prepared_unpacking as I _ v ⟨j,hj⟩]
  exact (UniformSectorPacking.unpackingPermutation as ⟨j,hj⟩).isLt
 have packedBound:∀j,j<(prepared x).1.1→(prepared x).1.2.1.look j 0<(prepared x).1.1:=by
  intro j hj
  rw [vol] at hj ⊢
  rw [prepared_packing as I _ v ⟨j,hj⟩]
  exact (UniformSectorPacking.packingPermutation as ⟨j,hj⟩).isLt
 have boolean:Boolean (packed x):=by
  have h:=move_boolean x.2.2.1 (prepared x).1.1 (prepared x).1.2.2.1 x.2.2.2 before
  rw [move_value] at h
  exact h
 have roles:1≤UniformBatching.width:=by
  rw [UniformBatching.width_eq_pow]
  exact Nat.two_pow_pos _
 rw [program_peak_stages]
 refine max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_)))
 · exact (DFTModelGlobalSectorPreparation.withDirectory_peak as).trans
    (by unfold peakBudget;dsimp only [V];omega)
 · exact (move_peak _ _ _ _ unpacked).trans (by change UniformBatching.width*(prepared x).1.1≤_;rw [vol];exact wb)
 · rw [sectors_peak]
   refine max_le ((prepared_count as I _ v).trans (vol.le.trans vb)) ?_
   apply Finset.sup_le
   intro j hj
   have shape:=prepared_shape as I UniformBatching.width v j (Finset.mem_range.mp hj)
   dsimp only at shape
   dsimp only [sectorArgs]
   have fit:((prepared x).1.2.2.2.look j (0,(0,0))).2.2 +
     2^((prepared x).1.2.2.2.look j (0,(0,0))).1≤(prepared x).1.1:=by
    rw [←shape.1];exact shape.2.2
   have h:=DFTModelSectorTranspose.saving_peak
    ((prepared x).1.2.2.2.look j (0,(0,0))).1 (prepared x).1.1
    ((prepared x).1.2.2.2.look j (0,(0,0))).2.2 I (packed x) roles fit boolean
   apply h.trans
   apply max_le (by change UniformBatching.width*(prepared x).1.1≤_;rw [vol];exact wb)
   have fitV:=fit
   rw [vol] at fitV
   have powBound:2^((prepared x).1.2.2.2.look j (0,(0,0))).1≤V:=
    (Nat.le_add_left _ _).trans fitV
   exact (Nat.mul_le_mul_left DFTModelSavingPeak.wholeCoeff
    (Nat.mul_le_mul powBound powBound)).trans cb
 · have g:=DFTModelGlobalSectorPreparation.generated_geometry as
   have count:=DFTModelGlobalSectorPreparation.generated_count as
   rw [←prepared_directory as I UniformBatching.width v] at g count
   have h:=DFTModelSectorMaterialization.joined_peak Tagged (W:=UniformBatching.width) g count (compactPatches x) (packed x)
   apply h.trans
   rw [prepared_consistent,vol]
   exact mb
 · exact (move_peak _ _ _ _ packedBound).trans (by change UniformBatching.width*(prepared x).1.1≤_;rw [vol];exact wb)

def savingWork (x:Input.T) : ℕ :=
 ∑j∈Finset.range (prepared x).1.2.2.2.len,
  (run DFTModelSectorTranspose.saving
   (sectorArgs x.2.1 x.2.2.1 (prepared x).1.1 (prepared x).1.2.2.2 (packed x) j)).work

def overheadBudget (as:List UniformSectorPacking.Axis) (W:ℕ) : ℕ :=
 let V:=(UniformSectorPacking.radices as).prod
 10000*(W*V+V+as.length+DFTModelGlobalSectorPreparation.localBudget as+1)

/-- The arbitrary-axis bound keeps the honest quadratic local packing cost.
Selected-radix billing is a separate specialization to a real native run. -/
theorem program_work_bound (as:List UniformSectorPacking.Axis) (I:ℂ) (W:ℕ) (v:Tape Tagged.T) :
 (run program (nativeInput as I W v)).work≤
 overheadBudget as W+savingWork (nativeInput as I W v) := by
 have prep:=DFTModelGlobalSectorPreparation.withDirectory_work as
 have g:=DFTModelGlobalSectorPreparation.generated_geometry as
 have count:=DFTModelGlobalSectorPreparation.generated_count as
 rw [←prepared_directory as I W v] at g count
 have material:=DFTModelSectorMaterialization.joined_work Tagged (W:=W) g count
  (compactPatches (nativeInput as I W v)) (packed (nativeInput as I W v))
 have sectors:=prepared_count as I W v
 have materialBound:=material.trans (show
  2200*((prepared (nativeInput as I W v)).2.1+W*(prepared (nativeInput as I W v)).2.1+1)≤
   2200*((UniformSectorPacking.radices as).prod+W*(UniformSectorPacking.radices as).prod+1) by
    rw [prepared_consistent,prepared_volume])
 change (run (DFTModelSectorMaterialization.joined Tagged)
  (W,((prepared (nativeInput as I W v)).2,
   (compactPatches (nativeInput as I W v),packed (nativeInput as I W v))))).work≤
   2200*((UniformSectorPacking.radices as).prod+W*(UniformSectorPacking.radices as).prod+1) at materialBound
 rw [prepared_volume] at sectors
 rw [program_work]
 change (run DFTModelGlobalSectorPreparation.withDirectory
  (ofList (as.map DFTModelGlobalSectorPreparation.encodeAxis))).work+
 106*(W*(prepared (nativeInput as I W v)).1.1)+
 68*(prepared (nativeInput as I W v)).1.2.2.2.len+savingWork (nativeInput as I W v)+
 (run (DFTModelSectorMaterialization.joined Tagged)
  (W,((prepared (nativeInput as I W v)).2,
   (compactPatches (nativeInput as I W v),packed (nativeInput as I W v))))).work+190≤_
 rw [prepared_volume]
 unfold overheadBudget
 dsimp only
 omega

theorem program_length (as:List UniformSectorPacking.Axis) (I:ℂ) (W:ℕ) (v:Tape Tagged.T) :
 (run program (nativeInput as I W v)).val.2.len=W*(UniformSectorPacking.radices as).prod := by
 rw [program_value]
 change W*(prepared (nativeInput as I W v)).1.1=_
 rw [prepared_volume]

theorem specification (as:List UniformSectorPacking.Axis) (I:ℂ) (v:Tape Tagged.T)
 (before:Boolean v) :
 let x:=nativeInput as I UniformBatching.width v
 (run program x).valid ∧
 (run program x).val.2.len=UniformBatching.width*(UniformSectorPacking.radices as).prod ∧
 Boolean (run program x).val.2 ∧
 (run program x).work≤overheadBudget as UniformBatching.width+savingWork x ∧
 (run program x).peak≤peakBudget as :=
 ⟨program_valid _ _ _ _,program_length _ _ _ _,program_boolean _ before,
  program_work_bound _ _ _ _,program_peak _ _ _ before⟩

end
end ExactFourierCircuits.DFTModelGlobalKernelAssembly

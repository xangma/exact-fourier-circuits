import DFTModelGlobalKernelAssemblyBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalKernelAssembly
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelCacheTraversal
noncomputable section

theorem prepared_sectors (as:List UniformSectorPacking.Axis) (I:ℂ) (W:ℕ) (v:Tape Tagged.T) :
 (prepared (nativeInput as I W v)).1.2.2.2=
 ofList ((UniformSectorPacking.sectorStates as).map DFTModelGlobalSectorPreparation.encodeSector) := by
 rw [prepared_first]
 exact (DFTModelGlobalSectorPreparation.program_native as).2.2.2.2.2

theorem prepared_packing (as:List UniformSectorPacking.Axis) (I:ℂ) (W:ℕ) (v:Tape Tagged.T)
 (j:Fin (UniformSectorPacking.radices as).prod) :
 (prepared (nativeInput as I W v)).1.2.1.look j.val 0=
 (UniformSectorPacking.packingPermutation as j).val := by
 rw [prepared_first]
 exact (DFTModelGlobalSectorPreparation.program_native as).2.2.2.1 j

theorem prepared_unpacking (as:List UniformSectorPacking.Axis) (I:ℂ) (W:ℕ) (v:Tape Tagged.T)
 (j:Fin (UniformSectorPacking.radices as).prod) :
 (prepared (nativeInput as I W v)).1.2.2.1.look j.val 0=
 (UniformSectorPacking.unpackingPermutation as j).val := by
 rw [prepared_first]
 exact (DFTModelGlobalSectorPreparation.program_native as).2.2.2.2.1 j

theorem moved_cell (W V role j:ℕ) (p:Tape ℕ) (v:Tape Tagged.T) (hr:role<W) (hj:j<V) :
 (moved W V p v).look (role*V+j) Tagged.blank=
 v.look (role*V+p.look j 0) Tagged.blank := by
 have vp:0<V:=by omega
 have live:role*V+j<W*V:=by nlinarith
 have rem:(role*V+j)%V=j:=by
  rw [Nat.mul_comm role V,Nat.mul_add_mod,Nat.mod_eq_of_lt hj]
 have div:(role*V+j)/V=role:=by
  rw [Nat.mul_comm role V,Nat.mul_add_div vp,Nat.div_eq_of_lt hj,Nat.add_zero]
 unfold moved
 rw [Tape.look_of_lt _ _ live]
 simp only [Tape.tab,rem,div]

/-- The generated inverse permutation is the actual original-address gather. -/
theorem packed_cell (as:List UniformSectorPacking.Axis) (I:ℂ) (W role:ℕ) (v:Tape Tagged.T)
 (hr:role<W) (j:Fin (UniformSectorPacking.radices as).prod) :
 (packed (nativeInput as I W v)).look
  (role*(UniformSectorPacking.radices as).prod+j.val) Tagged.blank=
 v.look (role*(UniformSectorPacking.radices as).prod+
  (UniformSectorPacking.unpackingPermutation as j).val) Tagged.blank := by
 unfold packed
 change (moved W (prepared (nativeInput as I W v)).1.1
  (prepared (nativeInput as I W v)).1.2.2.1 v).look _ _=_
 rw [prepared_volume,moved_cell _ _ _ _ _ _ hr j.isLt,prepared_unpacking]

/-- The generated packing table scatters the materialized bank back to original coordinates. -/
theorem returned_cell (as:List UniformSectorPacking.Axis) (I:ℂ) (W role:ℕ) (v:Tape Tagged.T)
 (hr:role<W) (j:Fin (UniformSectorPacking.radices as).prod) :
 (returned (nativeInput as I W v)).look
  (role*(UniformSectorPacking.radices as).prod+j.val) Tagged.blank=
 (materialized (nativeInput as I W v)).2.look
  (role*(UniformSectorPacking.radices as).prod+
   (UniformSectorPacking.packingPermutation as j).val) Tagged.blank := by
 unfold returned
 change (moved W (prepared (nativeInput as I W v)).1.1
  (prepared (nativeInput as I W v)).1.2.1 (materialized (nativeInput as I W v)).2).look _ _=_
 rw [prepared_volume,moved_cell _ _ _ _ _ _ hr j.isLt,prepared_packing]

theorem returned_packed_cell (as:List UniformSectorPacking.Axis) (I:ℂ) (W role:ℕ) (v:Tape Tagged.T)
 (hr:role<W) (j:Fin (UniformSectorPacking.radices as).prod) :
 (returned (nativeInput as I W v)).look
  (role*(UniformSectorPacking.radices as).prod+
   (UniformSectorPacking.unpackingPermutation as j).val) Tagged.blank=
 (materialized (nativeInput as I W v)).2.look
  (role*(UniformSectorPacking.radices as).prod+j.val) Tagged.blank := by
 rw [returned_cell as I W role v hr (UniformSectorPacking.unpackingPermutation as j)]
 have inv:UniformSectorPacking.packingPermutation as
   (UniformSectorPacking.unpackingPermutation as j)=j :=
  (UniformSectorPacking.packingPermutation as).apply_symm_apply j
 rw [inv]

/-- The final scattered bank contains the actual closed saving result at every
generated sector cell, in the original physical coordinate order. -/
theorem program_sector (as:List UniformSectorPacking.Axis) (I:ℂ) (W role i j:ℕ)
 (v:Tape Tagged.T) (hi:i<(UniformSectorPacking.sectorStates as).length)
 (hr:role<W) (hj:j<((UniformSectorPacking.sectorStates as)[i]'hi).width) :
 let st:=(UniformSectorPacking.sectorStates as)[i]'hi
 let V:=(UniformSectorPacking.radices as).prod
 let fit:=UniformSectorBatchDirectoryMachine.sector_fits as i hi
 (run program (nativeInput as I W v)).val.2.look
  (role*V+(UniformSectorPacking.unpackingPermutation as
    ⟨st.start+j,(Nat.add_lt_add_left hj st.start).trans_le fit⟩).val) Tagged.blank=
 (run DFTModelSectorTranspose.saving
  ((st.pairs,I),((W,(V,st.start)),packed (nativeInput as I W v)))).val.2.look
   (role*st.width+j) Tagged.blank := by
 dsimp only
 rw [program_value,returned_packed_cell as I W role v hr]
 unfold materialized
 have g:=DFTModelGlobalSectorPreparation.generated_geometry as
 have entry:(DFTModelGlobalSectorPreparation.generatedDirectory as).2.look i (0,0)=
   (((UniformSectorPacking.sectorStates as)[i]'hi).start,
    ((UniformSectorPacking.sectorStates as)[i]'hi).width) := by
  rw [DFTModelGlobalSectorPreparation.generated_directory]
  simp [ofList_look,hi]
 have count:i<(DFTModelGlobalSectorPreparation.generatedDirectory as).2.len:=by
  simpa [DFTModelGlobalSectorPreparation.generated_directory,ofList] using hi
 have h:=DFTModelSectorMaterialization.joined_sector Tagged g i role j
  (compactPatches (nativeInput as I W v)) (packed (nativeInput as I W v)) count hr
  (by simpa only [entry] using hj)
 rw [prepared_directory]
 rw [entry] at h
 have volume:(DFTModelGlobalSectorPreparation.generatedDirectory as).1=(UniformSectorPacking.radices as).prod:=by
  rw [DFTModelGlobalSectorPreparation.generated_directory]
 rw [volume] at h
 simp only [Nat.add_assoc] at h
 change (run (DFTModelSectorMaterialization.joined Tagged)
  (W,(((DFTModelGlobalSectorPreparation.generatedDirectory as).1,
   (DFTModelGlobalSectorPreparation.generatedDirectory as).2),
   (compactPatches (nativeInput as I W v),packed (nativeInput as I W v))))).val.2.look _ _=_
 rw [volume,h]
 have hp:(compactPatches (nativeInput as I W v)).look i (Tape.empty Tagged.T)=
   (run DFTModelSectorTranspose.saving
    (sectorArgs I W (UniformSectorPacking.radices as).prod
     (prepared (nativeInput as I W v)).1.2.2.2 (packed (nativeInput as I W v)) i)).val.2 := by
  unfold compactPatches patches
  have live:i<(prepared (nativeInput as I W v)).1.2.2.2.len:=by
   simpa [prepared_sectors,ofList] using hi
  simp only [Tape.look,Tape.tab,live,↓reduceDIte]
  rw [prepared_volume]
  rfl
 rw [hp]
 dsimp only [sectorArgs]
 rw [prepared_sectors]
 simp [ofList_look,hi,DFTModelGlobalSectorPreparation.encodeSector]

end
end ExactFourierCircuits.DFTModelGlobalKernelAssembly

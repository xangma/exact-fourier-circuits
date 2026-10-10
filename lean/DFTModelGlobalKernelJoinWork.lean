import DFTModelGlobalKernelJoinCore
set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalKernelJoin
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelCacheTraversal
open scoped BigOperators
noncomputable section
attribute [local irreducible] Code.run DFTModelGlobalKernelAssembly.program
 DFTModelSectorTranspose.saving DFTModelSectorMaterialization.joined
 DFTModelGlobalSectorPreparation.withDirectory DFTModelGlobalKernelAssembly.savingWork

lemma sum_look {α : Type} (xs : List α) (blank : α) (f : α→ℕ) :
 (∑j∈Finset.range xs.length,f ((ofList xs).look j blank))=(xs.map f).sum := by
 simp_rw [ofList_look]
 induction xs with
 | nil=>simp
 | cons x xs ih=>
  simp only[List.length_cons,Finset.sum_range_succ',List.getElem?_cons_zero,
   Option.getD_some,List.getElem?_cons_succ,List.map_cons,List.sum_cons]
  omega

lemma savings_eq {F : ℕ} (c : KS.Context F) (bank : Tape Tagged.T) :
 GA.savingWork (input c bank)=
 ((KS.states c).map (DFTModelGlobalSectorLoop.savingBill c.loop.volume (GA.packed (input c bank)))).sum := by
 have volume:c.loop.volume=c.packing.volume:=c.loopVolume.trans c.inverseVolume.symm
 have sectors : (GA.prepared (input c bank)).1.2.2.2=
  ofList ((KS.states c).map DFTModelGlobalSectorPreparation.encodeSector) :=
  DFTModelGlobalKernelAssembly.prepared_sectors (axes c) Complex.I KS.W bank
 have vol : (GA.prepared (input c bank)).1.1=c.packing.volume :=
  (DFTModelGlobalKernelAssembly.prepared_volume (axes c) Complex.I KS.W bank).trans c.physicalVolume
 unfold DFTModelGlobalKernelAssembly.savingWork
 change (∑j∈Finset.range (GA.prepared (input c bank)).1.2.2.2.len,
  (run DFTModelSectorTranspose.saving
   (DFTModelGlobalKernelAssembly.sectorArgs Complex.I KS.W (GA.prepared (input c bank)).1.1
    (GA.prepared (input c bank)).1.2.2.2 (GA.packed (input c bank)) j)).work)=_
 rw[sectors,vol]
 rw[show (ofList ((KS.states c).map DFTModelGlobalSectorPreparation.encodeSector)).len=
  (KS.states c).length by simp only[ofList,List.length_map]]
 have rows:
  (∑j∈Finset.range (KS.states c).length,
   (run DFTModelSectorTranspose.saving
    (DFTModelGlobalKernelAssembly.sectorArgs Complex.I KS.W c.packing.volume
     (ofList ((KS.states c).map DFTModelGlobalSectorPreparation.encodeSector))
     (GA.packed (input c bank)) j)).work)=
  ∑j∈Finset.range (KS.states c).length,
   DFTModelGlobalSectorLoop.savingBill c.loop.volume (GA.packed (input c bank))
    ((ofList (KS.states c)).look j ⟨0,0,0⟩) := by
  apply Finset.sum_congr rfl
  intro j hj
  have live:=Finset.mem_range.mp hj
  have mapped:j<((KS.states c).map DFTModelGlobalSectorPreparation.encodeSector).length:=by
   simpa only[List.length_map] using live
  simp only[DFTModelGlobalKernelAssembly.sectorArgs,DFTModelGlobalSectorLoop.savingBill,
   DFTModelGlobalSectorPreparation.encodeSector,ofList_look,
   List.getElem?_eq_getElem live,List.getElem?_eq_getElem mapped,Option.getD_some,List.getElem_map,volume]
 rw[rows,sum_look]

lemma gathered_lower {F n i K prepTicks loopTicks returnTicks : ℕ} (c : KS.Context F)
 {v v0 : ℕ→Fin c.packing.volume→UniformMachine.Scalar} {x : Fin n→ℂ}
 {s s0 a a0 t t0 z z0 : UniformMachine.State} {trace : List ℕ}
 (h : DFTModelGlobalKernelSource.Result (i:=i) c v v0 K x s s0 a a0 t t0 z z0 prepTicks loopTicks returnTicks trace) :
 KS.W*c.packing.volume≤prepTicks ∧c.packing.volume≤prepTicks ∧1≤prepTicks := by
 have lower:=h.gathers
 have widths:((KS.states c).map UniformSectorPacking.BlockState.width).sum=c.packing.volume:=by
  rw[DFTModelGlobalKernelSource.states,UniformProducedSectorChildABI.states,
   UniformSectorBatchDirectoryMachine.sector_width_sum]
  exact c.physicalVolume
 rw[DFTModelGlobalKernelSourceLower.gatherCost_sum,widths] at lower
 have positive:0<c.packing.volume:=by
  have p:=DFTModelGlobalSectorPreparation.native_volume_pos (axes c)
  simpa only[c.physicalVolume] using p
 have wp:1≤KS.W:=by
  change 1≤UniformBatching.width
  rw[UniformBatching.width_eq_pow]
  exact Nat.two_pow_pos _
 have pv:=Nat.mul_le_mul_right c.packing.volume wp
 rw[Nat.mul_assoc] at lower
 have total:KS.W*c.packing.volume≤prepTicks:=by omega
 simp only[one_mul] at pv
 exact ⟨total,pv.trans total,(Nat.succ_le_of_lt positive).trans (pv.trans total)⟩

/-- The entire closed typed kernel bill, not only its child sum, is paid
by this SAME complete native source execution. Selected shape is genuine
radix geometry; no packing, movement, materialization or execution budget is supplied. -/
theorem whole_work {F n i K prepTicks loopTicks returnTicks N : ℕ} (c : KS.Context F)
 {v v0 : ℕ→Fin c.packing.volume→UniformMachine.Scalar} {x : Fin n→ℂ}
 {s s0 a a0 t t0 z z0 : UniformMachine.State} {trace : List ℕ}
 (h : DFTModelGlobalKernelSource.Result (i:=i) c v v0 K x s s0 a a0 t t0 z z0 prepTicks loopTicks returnTicks trace)
 (hn : 0<N)
 (shape : UniformSectorPacking.radices (axes c)=List.ofFn (UniformSelectedCRT.radices N))
 (bank : Tape Tagged.T) (entry : Entry c bank v v0) :
 (run DFTModelGlobalKernelAssembly.program (input c bank)).work≤
 (K+DFTModelGlobalSectorBilling.preparationFactor+10000)*
  (prepTicks+(loopTicks+(returnTicks+1)+1)) := by
 let total:=prepTicks+(loopTicks+(returnTicks+1)+1)
 let inp:=input c bank
 have lower:=gathered_lower c h
 have wt:KS.W*c.packing.volume≤total:=lower.1.trans (by dsimp[total];omega)
 have vt:c.packing.volume≤total:=lower.2.1.trans (by dsimp[total];omega)
 have one:1≤total:=lower.2.2.trans (by dsimp[total];omega)
 have vol:(GA.prepared inp).1.1=c.packing.volume:=
  (DFTModelGlobalKernelAssembly.prepared_volume (axes c) Complex.I KS.W bank).trans c.physicalVolume
 have prep:=DFTModelGlobalSectorBilling.selected_work hn (axes c) shape
 have physical:(UniformSectorPacking.radices (axes c)).prod=c.packing.volume:=c.physicalVolume
 rw[physical] at prep
 have prepTotal:(run DFTModelGlobalSectorPreparation.withDirectory inp.1).work≤
  DFTModelGlobalSectorBilling.preparationFactor*total:=
  prep.trans (Nat.mul_le_mul_left _ vt)
 have count:=DFTModelGlobalKernelAssembly.prepared_count (axes c) Complex.I KS.W bank
 change (GA.prepared inp).1.2.2.2.len≤(GA.prepared inp).1.1 at count
 rw[vol] at count
 have countTotal:(GA.prepared inp).1.2.2.2.len≤total:=count.trans vt
 have g:=DFTModelGlobalSectorPreparation.generated_geometry (axes c)
 have mc:=DFTModelGlobalSectorPreparation.generated_count (axes c)
 have dir:(GA.prepared inp).2=DFTModelGlobalSectorPreparation.generatedDirectory (axes c):=rfl
 rw[←dir] at g mc
 have material:=DFTModelSectorMaterialization.joined_work Tagged (W:=KS.W) g mc
  (DFTModelGlobalKernelAssembly.compactPatches inp) (GA.packed inp)
 have consistent:(GA.prepared inp).2.1=c.packing.volume:=
  (DFTModelGlobalKernelAssembly.prepared_consistent (axes c) Complex.I KS.W bank).trans vol
 have materialTotal:
  (run (DFTModelSectorMaterialization.joined Tagged)
   (KS.W,((GA.prepared inp).2,(DFTModelGlobalKernelAssembly.compactPatches inp,GA.packed inp)))).work≤6600*total:=by
  apply material.trans
  rw[consistent]
  calc
   _≤2200*(3*total):=Nat.mul_le_mul_left _ (by omega)
   _=6600*total:=by ring
 have saving:=DFTModelGlobalKernelSource.Result.saving_work c h (GA.packed inp) (packed_encoded c bank v v0 entry)
 rw[←savings_eq] at saving
 change GA.savingWork inp≤(K+11)*total at saving
 have exactWork:=DFTModelGlobalKernelAssembly.program_work inp
 rw[←DFTModelGlobalKernelAssembly.savingWork] at exactWork
 simp only[show inp.2.2.1=KS.W from rfl,vol] at exactWork
 calc
  (run DFTModelGlobalKernelAssembly.program inp).work=
   (run DFTModelGlobalSectorPreparation.withDirectory inp.1).work+
   106*(KS.W*c.packing.volume)+68*(GA.prepared inp).1.2.2.2.len+GA.savingWork inp+
   (run (DFTModelSectorMaterialization.joined Tagged)
    (KS.W,((GA.prepared inp).2,(DFTModelGlobalKernelAssembly.compactPatches inp,GA.packed inp)))).work+190:=exactWork
  _≤DFTModelGlobalSectorBilling.preparationFactor*total+106*total+68*total+
   (K+11)*total+6600*total+190*total:=by
    have wm:=Nat.mul_le_mul_left 106 wt
    have cm:=Nat.mul_le_mul_left 68 countTotal
    have constant:=Nat.mul_le_mul_left 190 one
    omega
  _=(K+DFTModelGlobalSectorBilling.preparationFactor+6975)*total:=by ring
  _≤(K+DFTModelGlobalSectorBilling.preparationFactor+10000)*total:=
   Nat.mul_le_mul_right _ (by omega)

end
end ExactFourierCircuits.DFTModelGlobalKernelJoin

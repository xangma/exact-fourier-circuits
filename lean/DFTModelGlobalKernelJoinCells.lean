import DFTModelGlobalKernelJoinCore
set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalKernelJoin
open UniformMachine
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelRecursiveScalarSource
noncomputable section
attribute [local irreducible] DFTModelSectorTranspose.saving DFTModelGlobalKernelAssembly.program

/-- Canonical generated sectors cover every original coordinate. The SAME
closed child patch is read by both the native return and the typed assembly. -/
theorem whole_cells {F n i K prepTicks loopTicks returnTicks : ℕ} (c : KS.Context F)
 {v v0 : ℕ→Fin c.packing.volume→Scalar} {x : Fin n→ℂ}
 {s s0 a a0 t t0 z z0 : State} {trace : List ℕ}
 (h : DFTModelGlobalKernelSource.Result (i:=i) c v v0 K x s s0 a a0 t t0 z z0 prepTicks loopTicks returnTicks trace)
 (bank : Tape Tagged.T) (entry : Entry c bank v v0)
 (r : Fin KS.W) (j : Fin c.inverse.layout.total) :
 ∃out out0,
 z.scalarHeap (c.inverse.destination+r.val*c.inverse.layout.total+j.val)=some out ∧
 z0.scalarHeap (c.inverse.destination+r.val*c.inverse.layout.total+j.val)=some out0 ∧
 (run DFTModelGlobalKernelAssembly.program (input c bank)).val.2.look
  (r.val*c.inverse.layout.total+j.val) Tagged.blank=encodePaired out out0 := by
 let un:=UniformSectorPackingMachine.physicalUnpacking c.physical c.inverse.layout
  (c.physicalVolume.trans c.inverseVolume)
 let p:=un.symm j
 let q:Fin (UniformSectorPacking.radices (axes c)).prod:=
  (finCongr (c.physicalVolume.trans c.inverseVolume)).symm p
 obtain ⟨b,hb,k,hk,position⟩:=UniformGlobalInverseReturn.sector_cover (axes c) q
 have live:b<(KS.states c).length:=hb
 have width:((KS.states c)[b]'live).width=2^((KS.states c)[b]'live).pairs:=c.loop.pow b live
 have localFit:k<2^((KS.states c)[b]'live).pairs:=by rw[←width];exact hk
 obtain ⟨idx,idxv,out,out0,cell,cell0,value⟩:=
  DFTModelGlobalKernelSource.Result.sector_cells c h (GA.packed (input c bank))
   (packed_encoded c bank v v0 entry) b live r ⟨k,localFit⟩
 have idxeq:idx=p:=Fin.ext (idxv.trans position)
 have original:un idx=j:=by rw[idxeq];exact un.apply_symm_apply j
 have typed:=DFTModelGlobalKernelAssembly.program_sector (axes c) Complex.I KS.W r.val b k bank hb r.isLt hk
 dsimp only at typed
 have fit:=UniformSectorBatchDirectoryMachine.sector_fits (axes c) b hb
 let q':Fin (UniformSectorPacking.radices (axes c)).prod:=
  ⟨((UniformSectorPacking.sectorStates (axes c))[b]'hb).start+k,
   (Nat.add_lt_add_left hk _).trans_le fit⟩
 have same:q'=q:=Fin.ext position
 have originalTyped:(UniformSectorPacking.unpackingPermutation (axes c) q').val=j.val:=by
  rw[same]
  change (un p).val=j.val
  rw[Equiv.apply_symm_apply]
 have volume:(UniformSectorPacking.radices (axes c)).prod=c.inverse.layout.total:=
  c.physicalVolume.trans c.inverseVolume
 have loopVolume:c.loop.volume=c.inverse.layout.total:=c.loopVolume
 rw[originalTyped,volume] at typed
 change (run DFTModelGlobalKernelAssembly.program (input c bank)).val.2.look
  (r.val*c.inverse.layout.total+j.val) Tagged.blank=_ at typed
 have patch:
  (run DFTModelSectorTranspose.saving
   ((((KS.states c)[b]'live).pairs,Complex.I),
    ((KS.W,(c.inverse.layout.total,((KS.states c)[b]'live).start)),GA.packed (input c bank)))).val.2.look
   (r.val*((KS.states c)[b]'live).width+k) Tagged.blank=encodePaired out out0:=by
  rw[←loopVolume,width]
  exact value
 refine ⟨out,out0,?_,?_,typed.trans patch⟩
 · change z.scalarHeap (c.inverse.destination+r.val*c.inverse.layout.total+(un idx).val)=some out at cell
   rw[original] at cell
   exact cell
 · change z0.scalarHeap (c.inverse.destination+r.val*c.inverse.layout.total+(un idx).val)=some out0 at cell0
   rw[original] at cell0
   exact cell0

end
end ExactFourierCircuits.DFTModelGlobalKernelJoin

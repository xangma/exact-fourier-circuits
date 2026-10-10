import DFTModelGlobalKernelSourceExecution
set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalKernelSource
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (setPC)
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAdmissibilityControl DFTModelAffine DFTModelRecursiveScalarSource
noncomputable section

lemma sector_fits {F : ℕ} (c : Context F) :
 ∀st∈states c,st.start+2^st.pairs≤c.loop.volume := by
 intro st hs
 obtain ⟨i,hi,eq⟩:=List.getElem_of_mem hs
 subst st
 rw[←c.loop.pow i hi]
 exact c.loop.fits i hi

/-- Exact flag-preserving returned cells at original native coordinates.
The sector index is the same index used by the actual typed sector tab. -/
theorem Result.sector_cells {F n i K prepTicks loopTicks returnTicks : ℕ} (c : Context F)
 {v v0 : ℕ→Fin c.packing.volume→Scalar} {x : Fin n→ℂ} {s s0 a a0 t t0 z z0 : State} {trace : List ℕ}
 (h : Result (i:=i) c v v0 K x s s0 a a0 t t0 z z0 prepTicks loopTicks returnTicks trace)
 (bank : Tape Tagged.T)
 (encoded : DFTModelGlobalSectorLoop.Encoded c.loop.volume bank
  (UniformConditionalKernelLayout.packed c v) (UniformConditionalKernelLayout.packed c v0))
 (j : ℕ) (hj : j<(states c).length) (r : Fin W) (k : Fin (2^((states c)[j]'hj).pairs)) :
 ∃idx : Fin c.inverse.layout.total,idx.val=((states c)[j]'hj).start+k.val ∧
 ∃out out0,
 z.scalarHeap (c.inverse.destination+r.val*c.inverse.layout.total+
  (UniformSectorPackingMachine.physicalUnpacking c.physical c.inverse.layout
   (c.physicalVolume.trans c.inverseVolume) idx).val)=some out ∧
 z0.scalarHeap (c.inverse.destination+r.val*c.inverse.layout.total+
  (UniformSectorPackingMachine.physicalUnpacking c.physical c.inverse.layout
   (c.physicalVolume.trans c.inverseVolume) idx).val)=some out0 ∧
 (run DFTModelSectorTranspose.saving
  ((((states c)[j]'hj).pairs,Complex.I),((W,(c.loop.volume,((states c)[j]'hj).start)),bank))).val.2.look
  (r.val*2^((states c)[j]'hj).pairs+k.val) Tagged.blank=encodePaired out out0 := by
 have fit:=sector_fits c _ (List.getElem_mem hj)
 have bound : ((states c)[j]'hj).start+k.val<c.inverse.layout.total := by
  rw[←c.loopVolume];have:=k.isLt;omega
 let idx : Fin c.inverse.layout.total:=⟨((states c)[j]'hj).start+k.val,bound⟩
 obtain ⟨out,out0,cell,cell0,value⟩:=h.children.saving_cells bank encoded (sector_fits c) j hj r k
 have source:=completed_sources c h.children
 have sourceCell:=source.1 j hj r.val r.isLt k.val (by change k.val<((states c)[j]'hj).width;rw[c.loop.pow j hj];exact k.isLt)
 have sourceCell0:=source.2 j hj r.val r.isLt k.val (by change k.val<((states c)[j]'hj).width;rw[c.loop.pow j hj];exact k.isLt)
 simp only[UniformSectorTransposeMachine.sourceAddress,UniformAllSectorTransposeMachine.Geometry.local,
  ite_true,c.scatterBuffer,UniformAllSectorTransposeMachine.slice,c.loop.pow j hj] at sourceCell sourceCell0
 have outValue : returnedValues c t r.val (((states c)[j]'hj).start+k.val)=out :=
  Option.some.inj (sourceCell.symm.trans cell)
 have outValue0 : returnedValues c t0 r.val (((states c)[j]'hj).start+k.val)=out0 :=
  Option.some.inj (sourceCell0.symm.trans cell0)
 refine ⟨idx,rfl,out,out0,?_,?_,value⟩
 · have result:=h.returned.values r.val r.isLt
    (UniformSectorPackingMachine.physicalUnpacking c.physical c.inverse.layout
     (c.physicalVolume.trans c.inverseVolume) idx)
   simpa only[Equiv.symm_apply_apply,idx,outValue] using result
 · have result:=h.returned.values0 r.val r.isLt
    (UniformSectorPackingMachine.physicalUnpacking c.physical c.inverse.layout
     (c.physicalVolume.trans c.inverseVolume) idx)
   simpa only[Equiv.symm_apply_apply,idx,outValue0] using result

end
end ExactFourierCircuits.DFTModelGlobalKernelSource

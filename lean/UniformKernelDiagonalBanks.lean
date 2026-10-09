import UniformInitializedKernelRetention
import UniformDiagonalReturnNumeric
import UniformExecutedTaggedBank

set_option autoImplicit false
namespace ExactFourierCircuits.UniformKernelDiagonalBanks
open UniformMachine
noncomputable section
abbrev Kernel {W F R:ℕ}:=UniformConditionalKernelLayout.Context W F R
abbrev Diagonal (W:ℕ):=UniformGlobalDiagonalChildPrefix.Context W

/-- Ordinary shared-bank links only. Actual kernel frames will establish the
cache preservation; no desired transform or executable callback is a field. -/
structure Links {W F R:ℕ} (g:Kernel (W:=W) (F:=F) (R:=R)) (d:Diagonal W) where
 bound:d.metadata.B=g.metadata.B
 volume:g.packing.volume=d.packing.volume
 source:g.inverse.destination=d.tensor.source
 lane:d.lane=0
 natEnd:ℕ
 scalarEnd:ℕ
 directory:d.rows.directory+2*d.entries.length ≤ natEnd
 pools:∀a∈d.entries,a.pool+9*a.radix ≤ scalarEnd
 natPacking:natEnd ≤ g.packing.suffix
 natMetadata:natEnd ≤ g.metadata.rows
 natFresh:natEnd ≤ F
 natStack:natEnd ≤ g.inverse.layout.stack
 natInverse:natEnd ≤ g.inverse.layout.inverse
 scalarPacked:scalarEnd ≤ g.packing.destination
 scalarBuffer:scalarEnd ≤ g.gather.buffer
 scalarFresh:scalarEnd ≤ F
 scalarNative:scalarEnd ≤ g.scatter.native
 scalarTemporary:scalarEnd ≤ g.inverse.layout.destination
 scalarFinal:scalarEnd ≤ g.inverse.destination

lemma directory_transfer (D N:ℕ) (as:List UniformGlobalDiagonalRowsMachine.Entry) (i:ℕ) (s t:State)
 (ready:UniformGlobalDiagonalRowsMachine.Directory D as i s)
 (fit:D+2*(i+as.length) ≤ N) (kept:∀q,q < N→t.natHeap q=s.natHeap q):
 UniformGlobalDiagonalRowsMachine.Directory D as i t:=by
 induction as generalizing i with
 | nil=> trivial
 | cons a as ih=> 
  rcases ready with ⟨cell,tail⟩
  refine ⟨⟨?_,?_⟩,ih (i+1) tail (by simp only[List.length_cons] at fit;omega)⟩
  · exact (kept (D+2*i) (by simp only[List.length_cons] at fit;omega)).trans cell.1
  · exact (kept (D+2*i+1) (by simp only[List.length_cons] at fit;omega)).trans cell.2
lemma pools_transfer (S:ℕ) (as:List UniformGlobalDiagonalRowsMachine.Entry) (s t:State)
 (ready:UniformGlobalDiagonalRowsMachine.Pools as s)
 (fit:∀a∈as,a.pool+9*a.radix ≤ S) (kept:∀q,q < S→t.scalarHeap q=s.scalarHeap q):
 UniformGlobalDiagonalRowsMachine.Pools as t:=by
 intro a ha lane j
 have l:=lane.isLt
 have k:=j.isLt
 have endFit:=fit a ha
 have index:a.pool+lane.val*a.radix+j.val < S:=by nlinarith
 exact (kept _ index).trans (ready a ha lane j)

/-- Reindex the real physical kernel output to the diagonal traversal's
ordinary equal volume; the underlying coordinate integer stays unchanged. -/
def kernelValue {W F R:ℕ} (g:Kernel (W:=W) (F:=F) (R:=R)) (d:Diagonal W) (h:Links g d)
 (v:ℕ→Fin g.packing.volume→Scalar) (r:ℕ) (j:Fin d.packing.volume):ℂ:=
 (UniformSectorTensor.originalTensor (UniformSectorPackingMachine.physicalAxes g.physical)).mulVec
  (fun k=> (v r (finCongr g.physicalVolume k)).value)
  (finCongr (g.physicalVolume.trans h.volume).symm j)

lemma numeric_source {W F R:ℕ} (g:Kernel (W:=W) (F:=F) (R:=R)) (d:Diagonal W) (h:Links g d)
 (v:ℕ→Fin g.packing.volume→Scalar) (t:State)
 (stored:∀r,r < W→∀j:Fin (UniformSectorPackingMachine.physicalVolume g.physical),
  (t.scalarHeap (g.inverse.destination+r*UniformSectorPackingMachine.physicalVolume g.physical+j.val)).map Scalar.value=
   some ((UniformSectorTensor.originalTensor (UniformSectorPackingMachine.physicalAxes g.physical)).mulVec
    (fun k=> (v r (finCongr g.physicalVolume k)).value) j)):
 (∀r,r < W→∀j:Fin d.packing.volume,
  (UniformExecutedTaggedBank.values d.tensor.source d.tensor.volume t r j.val).value=kernelValue g d h v r j) ∧
 UniformGlobalTensorDiagonalMachine.Source d.tensor
  (UniformExecutedTaggedBank.values d.tensor.source d.tensor.volume t) t:=by
 have volume:UniformSectorPackingMachine.physicalVolume g.physical=d.tensor.volume:=
  (g.physicalVolume.trans h.volume).trans d.volume
 have all:∀r,r < W→∀j:Fin d.tensor.volume,
  (t.scalarHeap (d.tensor.source+r*d.tensor.volume+j.val)).map Scalar.value=
   some (kernelValue g d h v r (finCongr d.volume.symm j)):=by
  intro r hr j
  have saved:=stored r hr (finCongr volume.symm j)
  have same:finCongr volume.symm j=finCongr (g.physicalVolume.trans h.volume).symm (finCongr d.volume.symm j):=Fin.ext rfl
  unfold kernelValue
  rw[←same]
  simpa only[h.source,volume,finCongr_apply,Fin.val_cast] using saved
 refine ⟨?_,UniformExecutedTaggedBank.source d.tensor t _ all⟩
 intro r hr j
 have saved:=all r hr (finCongr d.volume j)
 have same:finCongr d.volume.symm (finCongr d.volume j)=j:=Fin.ext rfl
 rw[same] at saved
 exact UniformExecutedTaggedBank.value saved

end
end ExactFourierCircuits.UniformKernelDiagonalBanks

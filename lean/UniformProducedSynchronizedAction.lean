import UniformProducedAllAxisAlignment
import UniformProducedPhysicalCoordinate
import UniformPhysicalSynchronizedSchedule
import UniformKernelDiagonalSynchronizedAction
set_option autoImplicit false
namespace ExactFourierCircuits.UniformProducedSynchronizedAction
open UniformMachine UniformKernelDiagonalBanks
open UniformSynchronizedLayers
open UniformActualGlobalTickContext
noncomputable section

lemma reindex_action {ι κ:Type} [Fintype ι] [Fintype κ]
 (e:ι≃κ) (A:Matrix ι ι ℂ) (v:κ→ℂ) (j:ι):
 (Matrix.reindex e e A).mulVec v (e j)=A.mulVec (fun q=>v (e q)) j:=by
 change (A.submatrix e.symm e.symm).mulVec v (e j)=_
 rw[Matrix.submatrix_mulVec_equiv]
 simp only[Function.comp_def,Equiv.symm_symm,Equiv.symm_apply_apply]

lemma coordinate {n:ℕ} (f:UniformProducedAllAxisGeometry.Family n):
 (UniformPhysicalTensorFamily.coordinate
  (UniformSectorPackingMachine.physicalAxes (UniformProducedAllAxisGeometry.geometry f).physical)
  (UniformProducedAllAxisGeometry.index f) (radix n) (UniformProducedAllAxisGeometry.shape f)).trans
  (finCongr (UniformProducedAllAxisGeometry.volume f))=
 (UniformGenericPhysicalCoordinate.physical (radix n)).trans
  (finCongr (UniformSelectedCRT.radices_product n)):=by
 apply Equiv.ext
 intro ds
 apply Fin.ext
 change (UniformPhysicalTensorFamily.coordinate
  (UniformSectorPackingMachine.physicalAxes (UniformProducedAllAxisGeometry.geometry f).physical)
  (UniformProducedAllAxisGeometry.index f) (radix n) (UniformProducedAllAxisGeometry.shape f) ds).val=
  (UniformGenericPhysicalCoordinate.physical (radix n) ds).val
 have same:=congrArg Fin.val (UniformProducedPhysicalCoordinate.actual_family f ds)
 change _=_ at same
 exact same

/-- The actual K→147 consumer uses a constant physical MSB coordinate even
though matching partitions and physical axis records change at each clock. -/
theorem action {n H:ℕ} (hn:0<n) (f:UniformProducedAllAxisGeometry.Family n)
 (length:∀i,(localSchedules n i).length≤H) (t:Fin H)
 (localMatrices:∀i,Matrix.reindex (finCongr (UniformProducedAllAxisGeometry.shape f i))
   (finCongr (UniformProducedAllAxisGeometry.shape f i))
   (Matrix.diagonal (UniformProducedAllAxisAlignment.factors f i)*
    UniformMatchingKernelGeometry.localKernel
     ((UniformSectorPackingMachine.physicalAxes (UniformProducedAllAxisGeometry.geometry f).physical).get i))=
   (slot (localSchedules n (UniformProducedAllAxisGeometry.index f i))
    (length (UniformProducedAllAxisGeometry.index f i)) t).matrix)
 (v:ℕ→Fin (kernel hn (UniformProducedAllAxisGeometry.geometry f)).packing.volume→Scalar)
 (r:ℕ) (j:Fin (UniformActualGlobalTickContext.diagonal hn (UniformProducedAllAxisGeometry.geometry f)).packing.volume):
 UniformDiagonalReturnNumeric.multiplier (UniformActualGlobalTickContext.diagonal hn (UniformProducedAllAxisGeometry.geometry f)) j*
  kernelValue (kernel hn (UniformProducedAllAxisGeometry.geometry f))
   (UniformActualGlobalTickContext.diagonal hn (UniformProducedAllAxisGeometry.geometry f))
   (links hn (UniformProducedAllAxisGeometry.geometry f)) v r j=
 (UniformPhysicalSynchronizedSchedule.slot n H length t).mulVec (fun k=>(v r k).value) j:=by
 let g:=kernel hn (UniformProducedAllAxisGeometry.geometry f)
 let d:=UniformActualGlobalTickContext.diagonal hn (UniformProducedAllAxisGeometry.geometry f)
 let h:=links hn (UniformProducedAllAxisGeometry.geometry f)
 have actual:=UniformKernelDiagonalSynchronizedAction.action g d h
  (UniformProducedAllAxisGeometry.index f) (UniformProducedAllAxisGeometry.shape f)
  (UniformProducedAllAxisAlignment.factors f) (UniformProducedAllAxisAlignment.aligned hn f)
  (localSchedules n) length t localMatrices v r j
 let e:=finCongr (UniformProducedAllAxisGeometry.volume f)
 let q:=UniformPhysicalTensorFamily.coordinate
  (UniformSectorPackingMachine.physicalAxes (UniformProducedAllAxisGeometry.geometry f).physical)
  (UniformProducedAllAxisGeometry.index f) (radix n) (UniformProducedAllAxisGeometry.shape f)
 let A:=Matrix.reindex q q (tensorSlot (localSchedules n) length t)
 have numeric:UniformDiagonalReturnNumeric.multiplier d j*kernelValue g d h v r j=
  A.mulVec (fun k=>(v r (e k)).value) (e.symm j):=actual
 have transport:=reindex_action e A (fun k=>(v r k).value) (e.symm j)
 change (Matrix.reindex e e A).mulVec (fun k=>(v r k).value) j=_ at transport
 have matrices:Matrix.reindex e e A=UniformPhysicalSynchronizedSchedule.slot n H length t:=by
  change Matrix.reindex (q.trans e) (q.trans e) (tensorSlot (localSchedules n) length t)=_
  have eq:=coordinate f
  change q.trans e=_ at eq
  rw[eq]
  rfl
 exact numeric.trans (transport.symm.trans (congrArg (fun M=>M.mulVec (fun k=>(v r k).value) j) matrices))
end
end ExactFourierCircuits.UniformProducedSynchronizedAction

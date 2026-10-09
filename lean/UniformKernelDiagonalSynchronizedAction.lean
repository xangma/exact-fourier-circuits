import UniformPhysicalTensorFamily
import UniformKernelDiagonalTensorAction
import UniformSynchronizedLayers
set_option autoImplicit false
namespace ExactFourierCircuits.UniformKernelDiagonalSynchronizedAction
open UniformMachine UniformKernelDiagonalBanks UniformKernelDiagonalTensorAction
open OAI.ExactFourier
noncomputable section

/-- Per-axis generated calendar semantics suffice to identify the real
common-C plus diagonal operation with one simultaneous synchronized slot. -/
theorem action {W F R:ℕ} {ι:Type} [Fintype ι] [DecidableEq ι] {r:ι→ℕ} {T:ℕ}
 (g:Kernel (W:=W) (F:=F) (R:=R)) (d:Diagonal W) (links:Links g d)
 (index:Fin (physical g).length≃ι) (shape:∀i,((physical g).get i).widths.sum=r (index i))
 (a:∀i:Fin (physical g).length,Fin ((physical g).get i).widths.sum→ℂ) (aligned:Aligned g d a)
 (L:∀i,List (UniformLocalFourierLayers.Layer (r i))) (length:∀i,(L i).length≤T) (t:Fin T)
 (localMatrices:∀i,Matrix.reindex (finCongr (shape i)) (finCongr (shape i))
   (Matrix.diagonal (a i)*UniformMatchingKernelGeometry.localKernel ((physical g).get i))=
   (UniformSynchronizedLayers.slot (L (index i)) (length (index i)) t).matrix)
 (v:ℕ→Fin g.packing.volume→Scalar) (role:ℕ) (j:Fin d.packing.volume):
 UniformDiagonalReturnNumeric.multiplier d j*kernelValue g d links v role j=
 (Matrix.reindex (UniformPhysicalTensorFamily.coordinate (physical g) index r shape)
   (UniformPhysicalTensorFamily.coordinate (physical g) index r shape)
   (UniformSynchronizedLayers.tensorSlot L length t)).mulVec
  (fun k=>(v role (finCongr g.physicalVolume k)).value)
  (finCongr (g.physicalVolume.trans links.volume).symm j):=by
 have matrices:=UniformPhysicalTensorFamily.tensor (physical g) index r shape
  (fun i=>Matrix.diagonal (a i)*UniformMatchingKernelGeometry.localKernel ((physical g).get i))
  (fun i=>(UniformSynchronizedLayers.slot (L i) (length i) t).matrix) localMatrices
 change _=(Matrix.reindex _ _ (PiTensor.matrix _)).mulVec _ _
 rw[matrices]
 exact UniformKernelDiagonalTensorAction.action g d links a aligned v role j

/-- This gives the numeric interpretation of real output cells after the
already proved physical consumer, with no desired global-output premise. -/
theorem stored {W F R:ℕ} {ι:Type} [Fintype ι] [DecidableEq ι] {r:ι→ℕ} {T:ℕ}
 (g:Kernel (W:=W) (F:=F) (R:=R)) (d:Diagonal W) (links:Links g d)
 (index:Fin (physical g).length≃ι) (shape:∀i,((physical g).get i).widths.sum=r (index i))
 (a:∀i:Fin (physical g).length,Fin ((physical g).get i).widths.sum→ℂ) (aligned:Aligned g d a)
 (L:∀i,List (UniformLocalFourierLayers.Layer (r i))) (length:∀i,(L i).length≤T) (t:Fin T)
 (localMatrices:∀i,Matrix.reindex (finCongr (shape i)) (finCongr (shape i))
   (Matrix.diagonal (a i)*UniformMatchingKernelGeometry.localKernel ((physical g).get i))=
   (UniformSynchronizedLayers.slot (L (index i)) (length (index i)) t).matrix)
 (v:ℕ→Fin g.packing.volume→Scalar) (u:State)
 (values:∀role,role<W→∀j:Fin d.packing.volume,
   (u.scalarHeap (d.tensor.source+role*d.tensor.volume+j.val)).map Scalar.value=
   some (UniformDiagonalReturnNumeric.multiplier d j*kernelValue g d links v role j)):
 ∀role,role<W→∀j:Fin d.packing.volume,
 (u.scalarHeap (d.tensor.source+role*d.tensor.volume+j.val)).map Scalar.value=
 some ((Matrix.reindex (UniformPhysicalTensorFamily.coordinate (physical g) index r shape)
   (UniformPhysicalTensorFamily.coordinate (physical g) index r shape)
   (UniformSynchronizedLayers.tensorSlot L length t)).mulVec
  (fun k=>(v role (finCongr g.physicalVolume k)).value)
  (finCongr (g.physicalVolume.trans links.volume).symm j)):=by
 intro role hrole j
 rw[values role hrole j,action g d links index shape a aligned L length t localMatrices v role j]
end
end ExactFourierCircuits.UniformKernelDiagonalSynchronizedAction

import UniformPhysicalTensorCoefficient
import UniformActualKernelDiagonalExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformKernelDiagonalTensorAction
open UniformMachine UniformKernelDiagonalBanks
open scoped BigOperators
noncomputable section

abbrev physical {W F R:ℕ} (g:Kernel (W:=W) (F:=F) (R:=R)):=
 UniformSectorPackingMachine.physicalAxes g.physical
abbrev monomial {W:ℕ} (d:Diagonal W):=
 UniformGlobalDiagonalRowsMachine.axes d.lane d.rows.permutation d.rows.coefficient 0 d.entries

def Aligned {W F R:ℕ} (g:Kernel (W:=W) (F:=F) (R:=R)) (d:Diagonal W)
 (a:∀i:Fin (physical g).length,Fin ((physical g).get i).widths.sum→ℂ):Prop:=
 List.Forall₂ UniformPhysicalTensorCoefficient.CoefficientEq (monomial d)
  (UniformPhysicalTensorCoefficient.axes (physical g) a)

def coordinate {W F R:ℕ} (g:Kernel (W:=W) (F:=F) (R:=R)) (d:Diagonal W) (links:Links g d):
 ((i:Fin (physical g).length)→Fin ((physical g).get i).widths.sum)≃Fin d.packing.volume:=
 (UniformPhysicalTensorPi.coordinate (physical g)).trans (finCongr (g.physicalVolume.trans links.volume))

/-- The real147 multiplier uses exactly the same coordinate as the actual
common-C gather/scatter. Only the individual produced pool lane values enter. -/
theorem multiplier {W F R:ℕ} (g:Kernel (W:=W) (F:=F) (R:=R)) (d:Diagonal W) (links:Links g d)
 (a:∀i:Fin (physical g).length,Fin ((physical g).get i).widths.sum→ℂ)
 (aligned:Aligned g d a) (j:Fin d.packing.volume):
 UniformDiagonalReturnNumeric.multiplier d j=
 ∏i:Fin (physical g).length,a i ((coordinate g d links).symm j i):=by
 have result:=UniformPhysicalTensorCoefficient.aligned_coefficient (monomial d) (physical g) a aligned
  (finCongr (g.physicalVolume.trans links.volume).symm j)
 change UniformTensorMonomialMachine.tensorCoefficient (monomial d) _=_
 exact (congrArg (UniformTensorMonomialMachine.tensorCoefficient (monomial d)) (Fin.ext rfl)).trans result

/-- This is the complete numerical operation of the proved common-C consumer
and actual147 diagonal, in the tensor coordinate of every printed physical axis. -/
theorem action {W F R:ℕ} (g:Kernel (W:=W) (F:=F) (R:=R)) (d:Diagonal W) (links:Links g d)
 (a:∀i:Fin (physical g).length,Fin ((physical g).get i).widths.sum→ℂ)
 (aligned:Aligned g d a) (v:ℕ→Fin g.packing.volume→Scalar) (r:ℕ) (j:Fin d.packing.volume):
 UniformDiagonalReturnNumeric.multiplier d j*kernelValue g d links v r j=
 (Matrix.reindex (UniformPhysicalTensorPi.coordinate (physical g)) (UniformPhysicalTensorPi.coordinate (physical g))
   (OAI.ExactFourier.PiTensor.matrix (fun i:Fin (physical g).length=>
    Matrix.diagonal (a i)*UniformMatchingKernelGeometry.localKernel ((physical g).get i)))).mulVec
   (fun k=>(v r (finCongr g.physicalVolume k)).value)
   (finCongr (g.physicalVolume.trans links.volume).symm j):=by
 rw[UniformPhysicalTensorPi.diagonal_kernel,←Matrix.mulVec_mulVec,Matrix.mulVec_diagonal]
 exact congrArg (fun z=>z*kernelValue g d links v r j) (multiplier g d links a aligned j)

/-- Genuine produced numeric output can therefore be read directly as the
all-axis tensor action, without an assumed child transform or output value. -/
theorem stored {W F R:ℕ} (g:Kernel (W:=W) (F:=F) (R:=R)) (d:Diagonal W) (links:Links g d)
 (a:∀i:Fin (physical g).length,Fin ((physical g).get i).widths.sum→ℂ)
 (aligned:Aligned g d a) (v:ℕ→Fin g.packing.volume→Scalar) (u:State)
 (values:∀r,r<W→∀j:Fin d.packing.volume,
   (u.scalarHeap (d.tensor.source+r*d.tensor.volume+j.val)).map Scalar.value=
   some (UniformDiagonalReturnNumeric.multiplier d j*kernelValue g d links v r j)):
 ∀r,r<W→∀j:Fin d.packing.volume,
  (u.scalarHeap (d.tensor.source+r*d.tensor.volume+j.val)).map Scalar.value=
   some ((Matrix.reindex (UniformPhysicalTensorPi.coordinate (physical g)) (UniformPhysicalTensorPi.coordinate (physical g))
    (OAI.ExactFourier.PiTensor.matrix (fun i:Fin (physical g).length=>
     Matrix.diagonal (a i)*UniformMatchingKernelGeometry.localKernel ((physical g).get i)))).mulVec
    (fun k=>(v r (finCongr g.physicalVolume k)).value)
    (finCongr (g.physicalVolume.trans links.volume).symm j)):=by
 intro r hr j
 rw[values r hr j,action g d links a aligned v r j]
end
end ExactFourierCircuits.UniformKernelDiagonalTensorAction

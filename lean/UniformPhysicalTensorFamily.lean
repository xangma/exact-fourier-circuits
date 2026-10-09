import UniformPhysicalTensorPi
set_option autoImplicit false
namespace ExactFourierCircuits.UniformPhysicalTensorFamily
open scoped BigOperators
open OAI.ExactFourier
noncomputable section

/-- Finite axis enumeration and coordinate transports affect neither the tensor
entries nor the order of the genuine matrix multiplication within each axis. -/
theorem pi_reindex {ι κ:Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
 {D:ι→Type} {E:κ→Type} [∀i,Fintype (D i)] [∀i,Fintype (E i)]
 [∀i,DecidableEq (D i)] [∀i,DecidableEq (E i)]
 (index:ι≃κ) (fields:∀i,D i≃E (index i))
 (A:∀i,Matrix (D i) (D i) ℂ) (B:∀i,Matrix (E i) (E i) ℂ)
 (same:∀i,Matrix.reindex (fields i) (fields i) (A i)=B (index i)):
 Matrix.reindex (Equiv.piCongr index fields) (Equiv.piCongr index fields) (PiTensor.matrix A)=PiTensor.matrix B:=by
 classical
 ext x y
 simp only[Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.piCongr_symm_apply,PiTensor.matrix]
 apply Fintype.prod_equiv index
 intro i
 exact congrFun (congrFun (same i) (x (index i))) (y (index i))

def coordinate {ι:Type} (ps:List UniformSectorPacking.Axis) (index:Fin ps.length≃ι)
 (r:ι→ℕ) (shape:∀i,(ps.get i).widths.sum=r (index i)):
 (∀i,Fin (r i))≃Fin (UniformSectorPacking.radices ps).prod:=
 (Equiv.piCongr index (fun i=>finCongr (shape i))).symm.trans (UniformPhysicalTensorPi.coordinate ps)

/-- A list of genuinely printed physical axes lifts to the actual synchronized
axis family under its finite enumeration and ordinary radix equalities. -/
theorem tensor {ι:Type} [Fintype ι] [DecidableEq ι]
 (ps:List UniformSectorPacking.Axis) (index:Fin ps.length≃ι)
 (r:ι→ℕ) (shape:∀i,(ps.get i).widths.sum=r (index i))
 (A:∀i:Fin ps.length,Matrix (Fin (ps.get i).widths.sum) (Fin (ps.get i).widths.sum) ℂ)
 (B:∀i,Matrix (Fin (r i)) (Fin (r i)) ℂ)
 (same:∀i,Matrix.reindex (finCongr (shape i)) (finCongr (shape i)) (A i)=B (index i)):
 Matrix.reindex (coordinate ps index r shape) (coordinate ps index r shape) (PiTensor.matrix B)=
 Matrix.reindex (UniformPhysicalTensorPi.coordinate ps) (UniformPhysicalTensorPi.coordinate ps) (PiTensor.matrix A):=by
 have familyEq:=pi_reindex index (fun i=>finCongr (shape i)) A B same
 rw[←familyEq]
 ext x y
 let q:((i:Fin ps.length)→Fin (ps.get i).widths.sum)≃((i:ι)→Fin (r i)):=
  Equiv.piCongr index (fun i=>finCongr (shape i))
 change PiTensor.matrix A
  (q.symm (q ((UniformPhysicalTensorPi.coordinate ps).symm x)))
  (q.symm (q ((UniformPhysicalTensorPi.coordinate ps).symm y)))=_
 simp only[Equiv.symm_apply_apply,Matrix.reindex_apply,Matrix.submatrix_apply]

/-- This directly transports the completed physical diagonal/common-C tensor
operation to any proved all-axis synchronized slot matrix. -/
theorem diagonal_kernel {ι:Type} [Fintype ι] [DecidableEq ι]
 (ps:List UniformSectorPacking.Axis) (index:Fin ps.length≃ι)
 (r:ι→ℕ) (shape:∀i,(ps.get i).widths.sum=r (index i))
 (d:∀i:Fin ps.length,Fin (ps.get i).widths.sum→ℂ)
 (B:∀i,Matrix (Fin (r i)) (Fin (r i)) ℂ)
 (same:∀i,Matrix.reindex (finCongr (shape i)) (finCongr (shape i))
  (Matrix.diagonal (d i)*UniformMatchingKernelGeometry.localKernel (ps.get i))=B (index i)):
 Matrix.reindex (coordinate ps index r shape) (coordinate ps index r shape) (PiTensor.matrix B)=
 Matrix.diagonal (fun p=>∏i,d i ((UniformPhysicalTensorPi.coordinate ps).symm p i))*
  UniformSectorTensor.originalTensor ps:=by
 rw[tensor ps index r shape _ B same,UniformPhysicalTensorPi.diagonal_kernel]
end
end ExactFourierCircuits.UniformPhysicalTensorFamily

import UniformMatchingKernelGeometry
import OAI.Computability.FourierCircuit.PiTensor
set_option autoImplicit false
namespace ExactFourierCircuits.UniformPhysicalTensorPi
open UniformSectorPacking UniformSectorTensor UniformMatchingKernelGeometry
open OAI.ExactFourier
open scoped BigOperators
noncomputable section

/-- The finite axis index has the same order as the actual printed axis list. -/
def digits:(axes:List Axis)→OriginalDigits axes→(i:Fin axes.length)→Fin (axes.get i).widths.sum
 | [],_=>fun i=>Fin.elim0 i
 | _a::axes,(x,xs)=>Fin.cases x (digits axes xs)
def undigits:(axes:List Axis)→((i:Fin axes.length)→Fin (axes.get i).widths.sum)→OriginalDigits axes
 | [],_=>()
 | _a::axes,f=>(f 0,undigits axes (fun i=>f i.succ))
lemma digits_undigits (axes:List Axis) (f:(i:Fin axes.length)→Fin (axes.get i).widths.sum):
 digits axes (undigits axes f)=f:=by
 induction axes with
 | nil=>funext i;exact Fin.elim0 i
 | cons a axes ih=>
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · rfl
  · exact congrFun (ih (fun j=>f j.succ)) j
lemma undigits_digits (axes:List Axis) (x:OriginalDigits axes):undigits axes (digits axes x)=x:=by
 induction axes with
 | nil=>cases x;rfl
 | cons a axes ih=>
  rcases x with ⟨x,xs⟩
  exact congrArg (fun tail=>(x,tail)) (ih xs)
def digitsEquiv (axes:List Axis):OriginalDigits axes ≃ ((i:Fin axes.length)→Fin (axes.get i).widths.sum):=
 ⟨digits axes,undigits axes,undigits_digits axes,digits_undigits axes⟩
/-- Explicit mixed radix with first axis most significant, exactly as the
physical traversal's list codec. This is only a semantic coordinate map. -/
def coordinate (axes:List Axis):((i:Fin axes.length)→Fin (axes.get i).widths.sum) ≃ Fin (radices axes).prod:=
 (digitsEquiv axes).symm.trans (mixedEquiv (radices axes))
lemma coordinate_symm (axes:List Axis) (x:OriginalDigits axes):
 (coordinate axes).symm (mixedEquiv (radices axes) x)=digits axes x:=by
 change digits axes ((mixedEquiv (radices axes)).symm (mixedEquiv (radices axes) x))=digits axes x
 rw[Equiv.symm_apply_apply]

lemma local_product (axes:List Axis) (x y:OriginalDigits axes):
 localTensor axes ((localDigitsEquiv axes).symm x) ((localDigitsEquiv axes).symm y)=
 ∏i:Fin axes.length,localKernel (axes.get i) (digits axes x i) (digits axes y i):=by
 induction axes with
 | nil=>simp[localTensor]
 | cons a axes ih=>
  rcases x with ⟨x,xs⟩
  rcases y with ⟨y,ys⟩
  change _=∏i:Fin (axes.length+1),localKernel ((a::axes).get i) (digits (a::axes) (x,xs) i) (digits (a::axes) (y,ys) i)
  rw[Fin.prod_univ_succ]
  change localKernel a x y * localTensor axes ((localDigitsEquiv axes).symm xs) ((localDigitsEquiv axes).symm ys)=
   localKernel a x y * ∏i:Fin axes.length,localKernel (axes.get i) (digits axes xs i) (digits axes ys i)
  exact congrArg (fun tail=>localKernel a x y*tail) (ih xs ys)

/-- All actual printed kernels act in one simultaneous tensor, including
every width-one identity and each local ordered permutation. -/
theorem original_pi (axes:List Axis):
 Matrix.reindex (coordinate axes) (coordinate axes)
  (PiTensor.matrix (fun i:Fin axes.length=>localKernel (axes.get i)))=originalTensor axes:=by
 ext u v
 obtain ⟨x,rfl⟩:=(mixedEquiv (radices axes)).surjective u
 obtain ⟨y,rfl⟩:=(mixedEquiv (radices axes)).surjective v
 simp only[Matrix.reindex_apply,Matrix.submatrix_apply,coordinate_symm,PiTensor.matrix,originalTensor,
  Equiv.symm_apply_apply]
 exact (local_product axes x y).symm
/-- Numerical action under the same explicit physical mixed-radix codec. -/
theorem original_action (axes:List Axis) (v:Fin (radices axes).prod→ℂ)
 (p:(i:Fin axes.length)→Fin (axes.get i).widths.sum):
 (originalTensor axes).mulVec v (coordinate axes p)=
 (PiTensor.matrix (fun i:Fin axes.length=>localKernel (axes.get i))).mulVec
  (fun q=>v (coordinate axes q)) p:=by
 rw[←original_pi]
 change ((PiTensor.matrix (fun i:Fin axes.length=>localKernel (axes.get i))).submatrix
  (coordinate axes).symm (coordinate axes).symm).mulVec v (coordinate axes p)=_
 rw[Matrix.submatrix_mulVec_equiv]
 simp only[Function.comp_def,Equiv.symm_symm,Equiv.symm_apply_apply]

lemma pi_diagonal {ι:Type} [Fintype ι] [DecidableEq ι] {D:ι→Type}
 [∀i,Fintype (D i)] [∀i,DecidableEq (D i)] (d:∀i,D i→ℂ):
 PiTensor.matrix (fun i=>Matrix.diagonal (d i))=Matrix.diagonal (fun p=>∏i,d i (p i)):=by
 classical
 ext p q
 by_cases same:p=q
 · subst q;simp[PiTensor.matrix]
 · simp only[PiTensor.matrix,Matrix.diagonal_apply]
   rw[ite_eq_right same]
   obtain ⟨i,different⟩:=Function.ne_iff.mp same
   exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right different)

/-- A synchronized tick's native diagonal followed by its printed physical
kernel equals the tensor of all local diagonal/kernel products. -/
theorem diagonal_kernel (axes:List Axis)
 (d:∀i:Fin axes.length,Fin (axes.get i).widths.sum→ℂ):
 Matrix.reindex (coordinate axes) (coordinate axes)
  (PiTensor.matrix (fun i:Fin axes.length=>Matrix.diagonal (d i)*localKernel (axes.get i)))=
 Matrix.diagonal (fun p=>∏i,d i ((coordinate axes).symm p i))*originalTensor axes:=by
 rw[show PiTensor.matrix (fun i:Fin axes.length=>Matrix.diagonal (d i)*localKernel (axes.get i))=
  PiTensor.matrix (fun i=>Matrix.diagonal (d i))*PiTensor.matrix (fun i=>localKernel (axes.get i)) from PiTensor.mul _ _]
 change (Matrix.reindexAlgEquiv ℂ ℂ (coordinate axes)) _=_
 rw[map_mul]
 change Matrix.reindex (coordinate axes) (coordinate axes) (PiTensor.matrix (fun i=>Matrix.diagonal (d i)))*
  Matrix.reindex (coordinate axes) (coordinate axes) (PiTensor.matrix (fun i=>localKernel (axes.get i)))=_
 rw[original_pi,pi_diagonal]
 congr 1
 ext p q
 simp only[Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.diagonal_apply,
  (coordinate axes).symm.injective.eq_iff]
end
end ExactFourierCircuits.UniformPhysicalTensorPi

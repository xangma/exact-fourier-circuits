import UniformPhysicalTensorPi
import UniformGlobalDiagonalRowsMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformPhysicalTensorCoefficient
open scoped BigOperators
open UniformSectorPacking
noncomputable section

lemma split_cast {r a b:ℕ} (h:a=b) (j:Fin (r*a)):
 finProdFinEquiv.symm (finCongr (congrArg (fun z=>r*z) h) j)=
 ((finProdFinEquiv.symm j).1,finCongr h (finProdFinEquiv.symm j).2):=by
 subst b
 rfl
lemma split_cast_pair {r a b:ℕ} (h:a=b) (x:Fin r) (y:Fin a):
 finProdFinEquiv.symm (finCongr (congrArg (fun z=>r*z) h) (finProdFinEquiv (x,y)))=
 (x,finCongr h y):=by
 subst b
 exact Equiv.symm_apply_apply finProdFinEquiv (x,y)

def axes : (ps:List Axis) → (∀i:Fin ps.length,Fin (ps.get i).widths.sum→ℂ) → List UniformTensorMonomialMachine.Axis
 | [],_=>[]
 | a::ps,d=>
   ⟨a.widths.sum,by have h:=a.radix_two;omega,Equiv.refl _,d 0,0,0⟩::
     axes ps (fun i=>d i.succ)
lemma radices (ps:List Axis) (d:∀i:Fin ps.length,Fin (ps.get i).widths.sum→ℂ):
 UniformTensorMonomialMachine.radices (axes ps d)=UniformSectorPacking.radices ps:=by
 induction ps with
 | nil=>rfl
 | cons a ps ih=>simpa only[axes,UniformTensorMonomialMachine.radices,List.map_cons] using congrArg (List.cons a.widths.sum) (ih (fun i=>d i.succ))

lemma mixed_coefficient (ps:List Axis) (d:∀i:Fin ps.length,Fin (ps.get i).widths.sum→ℂ)
 (x:OriginalDigits ps):
 UniformTensorMonomialMachine.tensorCoefficient (axes ps d)
  (finCongr (congrArg List.prod (radices ps d)).symm (mixedEquiv (UniformSectorPacking.radices ps) x))=
 ∏i:Fin ps.length,d i (UniformPhysicalTensorPi.digits ps x i):=by
 induction ps with
 | nil=>simp[UniformTensorMonomialMachine.tensorCoefficient,axes]
 | cons a ps ih=>
   rcases x with ⟨x,xs⟩
   change _=∏i:Fin (ps.length+1),d i (UniformPhysicalTensorPi.digits (a::ps) (x,xs) i)
   rw[Fin.prod_univ_succ]
   have codec:
    (finProdFinEquiv.symm
      (finCongr (congrArg List.prod (radices (a::ps) d)).symm
       (mixedEquiv (UniformSectorPacking.radices (a::ps)) (x,xs))))=
    (x,finCongr (congrArg List.prod (radices ps (fun i=>d i.succ))).symm
       (mixedEquiv (UniformSectorPacking.radices ps) xs)):=by
     exact split_cast_pair (congrArg List.prod (radices ps (fun i=>d i.succ))).symm x
       (mixedEquiv (UniformSectorPacking.radices ps) xs)
   exact (congrArg (fun z:Fin a.widths.sum × Fin (UniformTensorMonomialMachine.radices (axes ps (fun i=>d i.succ))).prod=>
     d 0 z.1 * UniformTensorMonomialMachine.tensorCoefficient (axes ps (fun i=>d i.succ)) z.2) codec).trans
     (congrArg (fun z=>d 0 x*z) (ih (fun i=>d i.succ) xs))

/-- This is the exact physical traversal coefficient in the explicit PiTensor coordinate. -/
theorem coefficient (ps:List Axis) (d:∀i:Fin ps.length,Fin (ps.get i).widths.sum→ℂ)
 (j:Fin (UniformSectorPacking.radices ps).prod):
 UniformTensorMonomialMachine.tensorCoefficient (axes ps d) (finCongr (congrArg List.prod (radices ps d)).symm j)=
 ∏i:Fin ps.length,d i ((UniformPhysicalTensorPi.coordinate ps).symm j i):=by
 obtain ⟨x,rfl⟩:=(mixedEquiv (UniformSectorPacking.radices ps)).surjective j
 rw[UniformPhysicalTensorPi.coordinate_symm]
 exact mixed_coefficient ps d x

/-- Coefficient equivalence deliberately forgets addresses and permutations: the
147 traversal multiplier only reads these radix-indexed scalar values. -/
def CoefficientEq (a b:UniformTensorMonomialMachine.Axis):Prop:=
 ∃h:a.radix=b.radix,∀j,a.coefficient j=b.coefficient (finCongr h j)
def EntryCoefficientEq (lane:Fin 9) (e:UniformGlobalDiagonalRowsMachine.Entry)
 (a:UniformTensorMonomialMachine.Axis):Prop:=
 ∃h:e.radix=a.radix,∀j,e.value lane j=a.coefficient (finCongr h j)
/-- Actual directory entries retain their real addresses; the semantic alignment
uses precisely their produced lane values, independent of those addresses. -/
lemma entry_axes {es:List UniformGlobalDiagonalRowsMachine.Entry} {ms:List UniformTensorMonomialMachine.Axis}
 (lane:Fin 9) (P C o:ℕ) (h:List.Forall₂ (EntryCoefficientEq lane) es ms):
 List.Forall₂ CoefficientEq (UniformGlobalDiagonalRowsMachine.axes lane P C o es) ms:=by
 induction h generalizing o with
 | nil=>exact .nil
 | @cons e a es ms h hs ih=>exact .cons h (ih (o+e.radix))

lemma equal_radices {as bs:List UniformTensorMonomialMachine.Axis} (h:List.Forall₂ CoefficientEq as bs):UniformTensorMonomialMachine.radices as=UniformTensorMonomialMachine.radices bs:=by
 induction h with
 | nil=>rfl
 | @cons a b as bs h hs ih=>
   obtain ⟨e,_⟩:=h
   exact congrArg₂ List.cons e ih

lemma tensor_congr {as bs:List UniformTensorMonomialMachine.Axis} (h:List.Forall₂ CoefficientEq as bs)
 (j:Fin (UniformTensorMonomialMachine.radices as).prod):
 UniformTensorMonomialMachine.tensorCoefficient as j=UniformTensorMonomialMachine.tensorCoefficient bs (finCongr (congrArg List.prod (equal_radices h)) j):=by
 induction h with
 | nil=>rfl
 | @cons a b as bs h hs ih=>
   have whole:=congrArg List.prod (equal_radices (List.Forall₂.cons h hs))
   obtain ⟨e,coeff⟩:=h
   rcases a with ⟨ra,pa,perma,ca,pA,cA⟩
   rcases b with ⟨rb,pb,permb,cb,pB,cB⟩
   dsimp only at e coeff
   subst rb
   have codec:
    finProdFinEquiv.symm (finCongr whole j)=
     ((finProdFinEquiv.symm j).1,
      finCongr (congrArg List.prod (equal_radices hs)) (finProdFinEquiv.symm j).2):=by
     exact split_cast (congrArg List.prod (equal_radices hs)) j
   simp only[UniformTensorMonomialMachine.tensorCoefficient]
   rw[codec]
   exact congrArg₂ (·*·) (coeff _) (ih _)

/-- Actual coefficient lists can be attached directly once their per-axis
produced lane values are identified. This contains no machine action premise. -/
theorem aligned_coefficient (ms:List UniformTensorMonomialMachine.Axis) (ps:List Axis)
 (d:∀i:Fin ps.length,Fin (ps.get i).widths.sum→ℂ)
 (h:List.Forall₂ CoefficientEq ms (axes ps d))
 (j:Fin (UniformSectorPacking.radices ps).prod):
 UniformTensorMonomialMachine.tensorCoefficient ms
  (finCongr (congrArg List.prod ((equal_radices h).trans (radices ps d))).symm j)=
 ∏i:Fin ps.length,d i ((UniformPhysicalTensorPi.coordinate ps).symm j i):=by
 rw[tensor_congr h]
 convert coefficient ps d j using 1
 congr 1

/-- Numerical coefficient multiplication agrees with the same explicit tensor
matrix used by actual physical sector gathering and scattering. -/
theorem aligned_matrix (ms:List UniformTensorMonomialMachine.Axis) (ps:List Axis)
 (d:∀i:Fin ps.length,Fin (ps.get i).widths.sum→ℂ)
 (h:List.Forall₂ CoefficientEq ms (axes ps d)):
 Matrix.diagonal (fun j=>UniformTensorMonomialMachine.tensorCoefficient ms
   (finCongr (congrArg List.prod ((equal_radices h).trans (radices ps d))).symm j))*
  UniformSectorTensor.originalTensor ps=
 Matrix.reindex (UniformPhysicalTensorPi.coordinate ps) (UniformPhysicalTensorPi.coordinate ps)
  (OAI.ExactFourier.PiTensor.matrix (fun i:Fin ps.length=>Matrix.diagonal (d i)*UniformMatchingKernelGeometry.localKernel (ps.get i))):=by
 rw[UniformPhysicalTensorPi.diagonal_kernel]
 have eq:(fun j=>UniformTensorMonomialMachine.tensorCoefficient ms
   (finCongr (congrArg List.prod ((equal_radices h).trans (radices ps d))).symm j))=
   (fun j=>∏i:Fin ps.length,d i ((UniformPhysicalTensorPi.coordinate ps).symm j i)):=
   funext (aligned_coefficient ms ps d h)
 rw[eq]
end
end ExactFourierCircuits.UniformPhysicalTensorCoefficient

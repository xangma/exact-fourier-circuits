import UniformSectorTransposeCoordinates
import UniformBinaryTensorCoordinates
/-!
Paper correspondence (audit): *An explicit power saving for the exact discrete Fourier transform*,
OpenAI math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
§4.3, proof of Proposition 4.2, PDF p. 20, and §4.2, Lemma 4.1, p. 19 (`prop:tensor-fourier`, `lem:sector-address`).

The paper does not name these integer bit codecs. They discharge the implementation obligation that each packed sector carries the child matrix in the literal within-sector order, including singleton axes and role-major batching.
-/

set_option autoImplicit false
namespace ExactFourierCircuits.UniformSectorPhysicalBinaryAction
open UniformMachine UniformSectorPacking UniformSectorTensor
open UniformBinaryTensorCoordinates
open scoped BigOperators
noncomputable section
/-- Numeric high-digit append. It has low k bits from the actual explicit
physical coordinates and the leading mixed-radix bit at weight2^k. -/
def highPoint (k:ℕ) (h:Fin 2) (low:Fin (2^k)):Fin (2^(k+1)):=
 (coordinates (k+1)).symm (Fin.snoc (coordinates k low) h)
lemma highPoint_value (k:ℕ) (h:Fin 2) (low:Fin (2^k)):
 (highPoint k h low).val=h.val*2^k+low.val:=by
 rw[highPoint,coordinates_inverse,Fin.sum_univ_castSucc]
 simp only[Fin.snoc_castSucc,Fin.val_castSucc,Fin.snoc_last,Fin.val_last]
 rw[←coordinates_inverse,Equiv.symm_apply_apply]
 ring
lemma physicalMatrix_high (k:ℕ) (h j:Fin 2) (low other:Fin (2^k)):
 physicalMatrix (k+1) (highPoint k h low) (highPoint k j other)=C h j*physicalMatrix k low other:=by
 rw[physicalMatrix_apply]
 simp only[highPoint,Equiv.apply_symm_apply]
 rw[Fin.prod_univ_castSucc]
 simp only[Fin.snoc_castSucc,Fin.snoc_last]
 rw[←physicalMatrix_apply]
 ring
lemma physicalMatrix_zero (x y:Fin (2^0)):physicalMatrix 0 x y=1:=by
 apply (physicalMatrix_apply 0 x y).trans
 apply Finset.prod_eq_one
 intro i _
 exact Fin.elim0 i
/- Lemma 4.1, (4.3), p. 19, plus Proposition 4.2 proof, p. 20: within-sector mixed-radix ordinals must agree with the recursive child’s binary coordinates. Bit-order equality is additional implementation bookkeeping. -/
/-- This is the actual mixed-radix within-sector ordinal, merely with its
proved width rewritten as2^q. There is no chosen/host permutation. -/
def physicalSector (axes:List Axis) (c:BlockChoices axes):Positions axes c ≃ Fin (2^sectorPairCount axes c):=
 (mixedEquiv (sectorRadices axes c)).trans (finCongr (sectorWidth_pow_two axes c))
lemma physicalSector_value (axes:List Axis) (c:BlockChoices axes) (x:Positions axes c):
 (physicalSector axes c x).val=UniformTraversal.encode (sectorRadices axes c) x:=
 mixedEquiv_value _ x
lemma physicalMatrix_cast (k l:ℕ) (h:k=l) (x y:Fin (2^k)):
 physicalMatrix l (finCongr (congrArg (fun k=>2^k) h) x) (finCongr (congrArg (fun k=>2^k) h) y)=physicalMatrix k x y:=by
 subst l;rfl
lemma physicalSector_two (axis:Axis) (axes:List Axis) (c:Fin axis.widths.length) (cs:BlockChoices axes)
 (h:axis.widths.get c=2) (x:Fin (axis.widths.get c)) (xs:Positions axes cs):
 finCongr (congrArg (fun k=>2^k) (UniformSectorNetworkAction.count_cons_two axis axes c cs h))
  (physicalSector (axis::axes) (c,cs) (x,xs))=
 highPoint (sectorPairCount axes cs) (finCongr h x) (physicalSector axes cs xs):=by
 apply Fin.ext
 change (physicalSector (axis::axes) (c,cs) (x,xs)).val=_
 calc
  _=UniformTraversal.encode (sectorRadices (axis::axes) (c,cs)) (x,xs):=physicalSector_value _ _ _
  _=x.val*2^sectorPairCount axes cs+UniformTraversal.encode (sectorRadices axes cs) xs:=by
   change x.val*(sectorRadices axes cs).prod+_=_
   rw[sectorWidth_pow_two]
  _=_:=by rw[highPoint_value,physicalSector_value];rfl
lemma physicalSector_one (axis:Axis) (axes:List Axis) (c:Fin axis.widths.length) (cs:BlockChoices axes)
 (h:axis.widths.get c=1) (x:Fin (axis.widths.get c)) (xs:Positions axes cs):
 finCongr (congrArg (fun k=>2^k) (UniformSectorNetworkAction.count_cons_one axis axes c cs h))
  (physicalSector (axis::axes) (c,cs) (x,xs))=physicalSector axes cs xs:=by
 apply Fin.ext
 change (physicalSector (axis::axes) (c,cs) (x,xs)).val=_
 have xv:x.val=0:=by have bound:x.val < axis.widths.get c:=x.isLt;omega
 calc
  _=UniformTraversal.encode (sectorRadices (axis::axes) (c,cs)) (x,xs):=physicalSector_value _ _ _
  _=UniformTraversal.encode (sectorRadices axes cs) xs:=by
   change x.val*(sectorRadices axes cs).prod+_=_
   rw[xv];simp
  _=_:=(physicalSector_value axes cs xs).symm
/-- The literal sector product equals the exact numeric child matrix, including
bit order and all singleton axes. Reversal of bit order is handled by the
actual highPoint product proof, not by an assumed runtime permutation. -/
theorem sectorTensor_physical (axes:List Axis) (c:BlockChoices axes) (x y:Positions axes c):
 sectorTensor axes c x y=physicalMatrix (sectorPairCount axes c) (physicalSector axes c x) (physicalSector axes c y):=by
 induction axes with
 | nil=>exact (physicalMatrix_zero (physicalSector [] c x) (physicalSector [] c y)).symm
 | cons axis axes ih=>
   rcases c with ⟨c,cs⟩
   rcases x with ⟨x,xs⟩
   rcases y with ⟨y,ys⟩
   rcases axis.widths_one_two (axis.widths.get c) (List.get_mem _ _) with h|h
   · have count:=UniformSectorNetworkAction.count_cons_one axis axes c cs h
     rw[←physicalMatrix_cast _ _ count,physicalSector_one axis axes c cs h x xs,
      physicalSector_one axis axes c cs h y ys]
     have xv:x.val=0:=by have bound:x.val < axis.widths.get c:=x.isLt;omega
     have yv:y.val=0:=by have bound:y.val < axis.widths.get c:=y.isLt;omega
     simpa [sectorTensor,blockEntry,h,xv,yv] using ih cs xs ys
   · have count:=UniformSectorNetworkAction.count_cons_two axis axes c cs h
     rw[←physicalMatrix_cast _ _ count,physicalSector_two axis axes c cs h x xs,
      physicalSector_two axis axes c cs h y ys,physicalMatrix_high]
     change blockEntry (axis.widths.get c) x.val y.val*sectorTensor axes cs xs ys=_
     rw[ih cs xs ys]
     congr 1
     have entry:=UniformSectorTensor.blockEntry_two (finCongr h x) (finCongr h y)
     change blockEntry 2 x.val y.val=C (finCongr h x) (finCongr h y) at entry
     simpa only[h] using entry
theorem sectorMatrix_physical (axes:List Axis) (c:BlockChoices axes):
 Matrix.reindex (physicalSector axes c) (physicalSector axes c) (sectorMatrix axes c)=physicalMatrix (sectorPairCount axes c):=by
 ext i j
 change sectorTensor axes c ((physicalSector axes c).symm i) ((physicalSector axes c).symm j)=_
 rw[sectorTensor_physical]
 simp only[Equiv.apply_symm_apply]
/- Theorem 2.6, pp. 11–12: recursion batches a fixed number of arbitrary arrays. These numeric coordinates implement that role-major batch ABI rather than adding a new matrix assumption. -/
/-- Literal role-major coordinates consumed by the4120..4123 child ABI. -/
def batchCoordinate (W:ℕ) (axes:List Axis) (c:BlockChoices axes):
 (Fin W×Positions axes c) ≃ Fin (W*2^sectorPairCount axes c):=
 ((Equiv.refl _).prodCongr (physicalSector axes c)).trans finProdFinEquiv
lemma batchCoordinate_value (W:ℕ) (axes:List Axis) (c:BlockChoices axes) (r:Fin W) (x:Positions axes c):
 (batchCoordinate W axes c (r,x)).val=r.val*2^sectorPairCount axes c+
  UniformTraversal.encode (sectorRadices axes c) x:=by
 change (physicalSector axes c x).val+2^sectorPairCount axes c*r.val=_
 rw[physicalSector_value]
 ring
/-- Exact values of the W-array grouped operator in actual integer order. This
is an algebraic identity; it does not supply a recursive RAM child execution. -/
theorem batch_entries (W:ℕ) (axes:List Axis) (c:BlockChoices axes) (r s:Fin W) (x y:Positions axes c):
 (if r=s then sectorTensor axes c x y else 0)=
 (if r=s then physicalMatrix (sectorPairCount axes c) (physicalSector axes c x) (physicalSector axes c y) else 0):=by
 rw[sectorTensor_physical]
end
end ExactFourierCircuits.UniformSectorPhysicalBinaryAction

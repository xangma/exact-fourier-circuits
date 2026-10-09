import UniformPhysicalTensorFamily
set_option autoImplicit false
namespace ExactFourierCircuits.UniformPhysicalCoordinateValue
open UniformSectorPacking
open scoped BigOperators
noncomputable section

/-- The actual printed-list coordinate is first-axis most significant. Each
digit is multiplied by the product of the remaining printed radices. -/
theorem coordinate_value (ps:List Axis) (ds:∀i:Fin ps.length,Fin (ps.get i).widths.sum):
 ((UniformPhysicalTensorPi.coordinate ps) ds).val=
 ∑i:Fin ps.length,((radices ps).drop (i.val+1)).prod*(ds i).val:=by
 induction ps with
 | nil=>change (0:ℕ)=∑i:Fin 0,((radices []).drop (i.val+1)).prod*(ds i).val
        simp only[Finset.univ_eq_empty,Finset.sum_empty]
 | cons a ps ih=>
  change _=∑i:Fin (ps.length+1),((radices (a::ps)).drop (i.val+1)).prod*(ds i).val
  rw[Fin.sum_univ_succ]
  simp only[radices,List.map_cons,Fin.val_zero,Nat.zero_add,List.drop_succ_cons,Fin.val_succ]
  change ((UniformPhysicalTensorPi.coordinate ps) (fun i=>ds i.succ)).val+
   (radices ps).prod*(ds 0).val=
   (radices ps).prod*(ds 0).val+∑i:Fin ps.length,((radices ps).drop (i.val+1)).prod*(ds i.succ).val
  rw[ih]
  exact Nat.add_comm _ _

/-- Finite axis renaming and radix casts preserve those exact physical digit
values; this formula makes no identification with the normal LSB CRT codec. -/
theorem family_value {ι:Type} (ps:List Axis) (index:Fin ps.length≃ι)
 (r:ι→ℕ) (shape:∀i,(ps.get i).widths.sum=r (index i)) (ds:∀i,Fin (r i)):
 ((UniformPhysicalTensorFamily.coordinate ps index r shape) ds).val=
 ∑i:Fin ps.length,((radices ps).drop (i.val+1)).prod*(ds (index i)).val:=by
 change ((UniformPhysicalTensorPi.coordinate ps)
  ((Equiv.piCongr index (fun i=>finCongr (shape i))).symm ds)).val=_
 rw[coordinate_value]
 have castval {a b:ℕ} (h:a=b) (x:Fin b):((finCongr h).symm x).val=x.val:=by
  subst b;rfl
 simp only[Equiv.piCongr_symm_apply,castval]
end
end ExactFourierCircuits.UniformPhysicalCoordinateValue

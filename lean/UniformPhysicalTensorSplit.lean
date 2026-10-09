import UniformBinarySpectatorCMachine
import UniformNativeCopiedInverse
set_option autoImplicit false
namespace ExactFourierCircuits.UniformPhysicalTensorSplit
open OAI.ExactFourier UniformBinaryTensorCoordinates UniformNativeCopiedInverse
open scoped BigOperators Kronecker
noncomputable section

lemma split_address (k r : ℕ) (s : Fin (2^r)) (z : Fin (2^k)) :
 ((spectatorSplit k r).symm (s,z)).val=z.val+2^k*s.val := by
 simp [spectatorSplit,finProdFinEquiv,Nat.mul_comm]

lemma split_low_digit (k r : ℕ) (s : Fin (2^r)) (z : Fin (2^k)) (i : Fin k) :
 coordinates (k+r) ((spectatorSplit k r).symm (s,z)) (Fin.castAdd r i)=
 coordinates k z i := by
 apply Fin.ext
 rw [coordinates_value,coordinates_value,split_address]
 change (z.val+2^k*s.val)/2^i.val%2=z.val/2^i.val%2
 rw [←Nat.mod_mul_right_div_self,←Nat.mod_mul_right_div_self]
 have hd : 2^i.val*2 ∣ 2^k := by
  rw [←Nat.pow_succ]
  exact Nat.pow_dvd_pow 2 (by omega)
 rw [Nat.add_mod,Nat.mul_mod,Nat.mod_eq_zero_of_dvd hd]
 simp only [Nat.zero_mul,Nat.zero_mod,Nat.add_zero,Nat.mod_mod]

lemma split_high_digit (k r : ℕ) (s : Fin (2^r)) (z : Fin (2^k)) (i : Fin r) :
 coordinates (k+r) ((spectatorSplit k r).symm (s,z)) (Fin.natAdd k i)=
 coordinates r s i := by
 apply Fin.ext
 rw [coordinates_value,coordinates_value,split_address]
 change (z.val+2^k*s.val)/2^(k+i.val)%2=s.val/2^i.val%2
 rw [Nat.pow_add,←Nat.div_div_eq_div_mul,
   Nat.add_mul_div_left _ _ (Nat.two_pow_pos k),Nat.div_eq_of_lt z.isLt,Nat.zero_add]

/-- The real physical binary tensor splits into low and high digits, with
the high spectator coordinate outermost. No chosen coordinate map is used. -/
theorem physical_split (k r : ℕ) :
 physicalMatrix (k+r)=Matrix.reindex (spectatorSplit k r).symm (spectatorSplit k r).symm
  (physicalMatrix r ⊗ₖ physicalMatrix k) := by
 ext x y
 obtain ⟨⟨s,x⟩,rfl⟩ := (spectatorSplit k r).symm.surjective x
 obtain ⟨⟨t,y⟩,rfl⟩ := (spectatorSplit k r).symm.surjective y
 simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_symm,
  Equiv.apply_symm_apply,Matrix.kroneckerMap_apply]
 rw [physicalMatrix_apply,Fin.prod_univ_add]
 simp only [split_low_digit,split_high_digit]
 rw [mul_comm]
 rfl

def highMatrix (k r : ℕ) : Matrix (Fin (2^(k+r))) (Fin (2^(k+r))) ℂ :=
 Matrix.reindex (spectatorSplit k r).symm (spectatorSplit k r).symm
  (physicalMatrix r ⊗ₖ (1 : Matrix (Fin (2^k)) (Fin (2^k)) ℂ))

/-- Low C tensor followed by high C tensor is exactly the full physical C.
This closes the algebraic end of the complete record-plus-spectator schedule. -/
theorem low_high_tensor (k r : ℕ) :
 highMatrix k r * spectatorMatrix k r (physicalMatrix k)=physicalMatrix (k+r) := by
 unfold highMatrix spectatorMatrix
 rw [←PaddingWords.reindex_mul,←Matrix.mul_kronecker_mul,Matrix.mul_one,Matrix.one_mul,
  ←physical_split]

lemma axis_list_matrix (k : ℕ) (L : List (Fin k)) (nodup : L.Nodup) :
 ((L.map (axisMatrix k)).prod)=
 Matrix.reindex (coordinates k).symm (coordinates k).symm
  (PiTensor.matrix (fun i => if i∈L then C else (1 : Matrix (Fin 2) (Fin 2) ℂ))) := by
 classical
 let upd := fun i : Fin k => Function.update (1 : Fin k→Matrix (Fin 2) (Fin 2) ℂ) i C
 have values : (L.map upd).prod=(fun i => if i∈L then C else (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  funext i
  exact Embedded.list_update_prod (fun _ : Fin k => C) L nodup i
 have inner : (L.map (fun i => PiTensor.matrix (upd i))).prod=
  PiTensor.matrix (fun i => if i∈L then C else (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [show L.map (fun i => PiTensor.matrix (upd i))=(L.map upd).map PiTensor.hom from
    by rw [List.map_map];rfl]
  rw [←map_list_prod]
  change PiTensor.matrix ((L.map upd).prod)=_
  rw [values]
 have whole := congrArg (Matrix.reindex (coordinates k).symm (coordinates k).symm) inner
 unfold axisMatrix
 simpa [axisMatrix,upd,List.map_map,Function.comp_def] using
  ((Matrix.reindexAlgEquiv ℂ ℂ (coordinates k).symm).toMonoidHom.map_list_prod
   (L.map (fun i => PiTensor.matrix (upd i)))).symm.trans whole

lemma mem_low_axes (k r : ℕ) (i : Fin (k+r)) :
 i∈((List.finRange (k+r)).take k) ↔ i.val<k := by
 rw [List.mem_take_iff_getElem]
 constructor
 · rintro ⟨j,h,eq⟩
   have val := congrArg Fin.val eq
   simp only [List.getElem_finRange,Fin.val_cast] at val
   simp only [List.length_finRange] at h
   omega
 · intro h
   refine ⟨i.val,by simp only [List.length_finRange];omega,?_⟩
   apply Fin.ext
   simp only [List.getElem_finRange,Fin.val_cast]

lemma low_prefix_matrix (k r : ℕ) :
 ((((List.finRange (k+r)).take k).reverse).map (axisMatrix (k+r))).prod=
 spectatorMatrix k r (physicalMatrix k) := by
 classical
 rw [axis_list_matrix (k+r) _ (List.nodup_reverse.mpr ((List.nodup_finRange (k+r)).take))]
 simp only [List.mem_reverse,mem_low_axes]
 ext x y
 obtain ⟨⟨s,x⟩,rfl⟩ := (spectatorSplit k r).symm.surjective x
 obtain ⟨⟨t,y⟩,rfl⟩ := (spectatorSplit k r).symm.surjective y
 simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_symm,
  Equiv.apply_symm_apply,spectatorMatrix,Matrix.kroneckerMap_apply,Matrix.one_apply]
 change (∏i : Fin (k+r),
  (if i.val<k then C else (1 : Matrix (Fin 2) (Fin 2) ℂ))
   (coordinates (k+r) ((spectatorSplit k r).symm (s,x)) i)
   (coordinates (k+r) ((spectatorSplit k r).symm (t,y)) i))=
  (if s=t then 1 else 0)*physicalMatrix k x y
 rw [Fin.prod_univ_add]
 have lo (i : Fin k) : (i.castAdd r).val<k := i.isLt
 have hi (i : Fin r) : ¬(Fin.natAdd k i).val<k := by change ¬k+i.val<k;omega
 simp only [lo,hi,ite_true,ite_false,split_low_digit,split_high_digit]
 have highs : (∏i : Fin r,(1 : Matrix (Fin 2) (Fin 2) ℂ)
    (coordinates r s i) (coordinates r t i))=(if s=t then 1 else 0) := by
  change PiTensor.matrix (1 : Fin r→Matrix (Fin 2) (Fin 2) ℂ) (coordinates r s) (coordinates r t)=_
  rw [PiTensor.one,Matrix.one_apply]
  simp only [(coordinates r).injective.eq_iff]
 rw [highs,mul_comm]
 rfl

/-- The low block obtained from the compiled saving records is precisely the
actual little-endian axis prefix consumed by the frozen spectator machine. -/
theorem low_prefix_values (k r : ℕ) (v : Fin (2^(k+r))→UniformMachine.Scalar) :
 (fun z => (applyAxes (k+r) ((List.finRange (k+r)).take k) v z).value)=
 (spectatorMatrix k r (physicalMatrix k)).mulVec (fun z => (v z).value) := by
 rw [applyAxes_values,low_prefix_matrix]

end
end ExactFourierCircuits.UniformPhysicalTensorSplit

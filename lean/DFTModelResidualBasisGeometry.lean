import DFTModelResidualBasisImages

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelResidualBasisGeometry
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open BinaryFrames UniformBinaryXorCoordinates UniformResidualPermutation
open DFTModelResidualBasisImages
noncomputable section

/-- Concrete native representative-major, selected-q-bit-minor order, with
all remaining high spectator bits retained. -/
def permutation (q w r : ℕ) (v : Vec (Fin (w+1))) (p : Fin (w+1)) (hp : v p=1) :=
  UniformResidualSpectators.extend (q*(w+1)) r (UniformResidualPermutation.permutation q w v p hp)

theorem zero (q w r : ℕ) (v : Vec (Fin (w+1))) (p : Fin (w+1)) (hp : v p=1) :
    permutation q w r v p hp 0=0 :=
  UniformResidualSpectators.extend_zero _ _ _ (permutation_zero q w v p hp)

theorem xor (q w r : ℕ) (v : Vec (Fin (w+1))) (p : Fin (w+1)) (hp : v p=1)
    (a b : Fin (2^(q*(w+1)+r))) :
    permutation q w r v p hp (xorIndex a b)=
      xorIndex (permutation q w r v p hp a) (permutation q w r v p hp b) :=
  UniformResidualSpectators.extend_xor _ _ _ (permutation_xor q w v p hp) a b

theorem low_image (q w : ℕ) (v : Vec (Fin (w+1))) (p : Fin (w+1)) (hp : v p=1)
    (i : Fin (q*(w+1))) :
    imageValue q (w+1) (encode v).val p.val i.val=
      (UniformResidualPermutation.permutation q w v p hp (encode (unit i))).val := by
  by_cases low:i.val<q
  · have h:=selected_image q w v p hp (⟨i.val,low⟩:Fin q)
    simpa only [imageValue,exponentValue,ite_eq_left low] using h.symm
  · have hi:i.val-q<q*w := by
      have h:=i.isLt
      have h: i.val<q*w+q := by simpa only [Nat.mul_add,Nat.mul_one] using h
      omega
    let rep:Fin (q*w):=⟨i.val-q,hi⟩
    obtain ⟨⟨c,l⟩,hr⟩:=(finProdFinEquiv : Fin q×Fin w≃Fin (q*w)).surjective rep
    have iv:i.val=q+(finProdFinEquiv (c,l)).val := by rw [hr];simp [rep];omega
    have eqi:i=(⟨q+(finProdFinEquiv (c,l)).val,by
        rw [Nat.mul_add,Nat.mul_one];have h:=(finProdFinEquiv (c,l)).isLt;omega⟩:Fin (q*(w+1))) := Fin.ext iv
    have diff:i.val-q=(finProdFinEquiv (c,l)).val := by omega
    have wp:0<w := (Nat.zero_le l.val).trans_lt l.isLt
    have div:(i.val-q)/w=c.val := by
      rw [diff]
      simp [finProdFinEquiv,Nat.add_mul_div_left,Nat.div_eq_of_lt l.isLt,wp]
    have mod:(i.val-q)%w=l.val := by
      rw [diff]
      simp [finProdFinEquiv,Nat.mod_eq_of_lt l.isLt]
    have perm: (UniformResidualPermutation.permutation q w v p hp (encode (unit i))).val=
        2^(finProdFinEquiv (c,p.succAbove l)).val := by
      simpa only [←eqi] using representative_image q w v p hp c l
    rw [perm]
    have val: (if l.val<p.val then l.val else l.val+1)=(p.succAbove l).val := by
      by_cases lt:l.val<p.val
      · rw [Fin.succAbove_of_castSucc_lt p l (by exact lt)]
        simp [lt]
      · rw [Fin.succAbove_of_le_castSucc p l (by exact Nat.le_of_not_lt lt)]
        simp [lt]
    change imageValue q (w+1) (encode v).val p.val i.val=2^_
    simp only [imageValue,exponentValue,ite_eq_right low,ite_eq_left i.isLt,
      Nat.add_sub_cancel,Nat.mul_one]
    rw [div,mod,val]
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]

theorem image_value (q w r : ℕ) (v : Vec (Fin (w+1))) (p : Fin (w+1)) (hp : v p=1)
    (i : Fin (q*(w+1)+r)) :
    imageValue q (w+1) (encode v).val p.val i.val=
      (permutation q w r v p hp (encode (unit i))).val := by
  by_cases low:i.val<q*(w+1)
  · have h:=UniformResidualGeneralPreparation.low_image (q*(w+1)) r
      (UniformResidualPermutation.permutation q w v p hp) i.val low
    have hi:i.val<q*(w+1)+r:=i.isLt
    simp only [UniformResidualGeneralPreparation.image,dite_eq_left hi] at h
    exact (low_image q w v p hp ⟨i.val,low⟩).trans h.symm
  · have h:=UniformResidualGeneralPreparation.high_image (q*(w+1)) r
      (UniformResidualPermutation.permutation q w v p hp) (permutation_zero q w v p hp)
      i.val (by omega) i.isLt
    have hi:i.val<q*(w+1)+r:=i.isLt
    simp only [UniformResidualGeneralPreparation.image,dite_eq_left hi] at h
    have nonselected:¬i.val<q := by
      have bound:q≤q*(w+1):=by nlinarith
      omega
    simpa only [imageValue,exponentValue,ite_eq_right nonselected,ite_eq_right low,Nat.mul_one,permutation] using h.symm

/-- The supplied raw direction determines every image of the actual basis
materializer; no supplied image bank remains in this contract. -/
theorem program_images (q w r : ℕ) (v : Vec (Fin (w+1))) (p : Fin (w+1)) (hp : v p=1) :
    ∀i:Fin (q*(w+1)+r),
      (run program (q,(w+1,(r,((encode v).val,p.val))))).val.look i.val 0=
        (permutation q w r v p hp (encode (unit i))).val := by
  intro i
  rw [program_value]
  simpa only [Tape.look,Tape.tab,i.isLt,↓reduceDIte] using image_value q w r v p hp i

end
end ExactFourierCircuits.DFTModelResidualBasisGeometry

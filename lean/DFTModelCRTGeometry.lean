import DFTModelCRTRecursion
import UniformPhysicalCRTCoordinates

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCRT
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformGenericPhysicalCoordinate
open scoped BigOperators
noncomputable section

/-- Every fresh suffix table is charged; their total size is geometric. -/
theorem prefix_volumeSum_le (k : ℕ) (x : Args.T)
    (h : ∀ i < k, 2 ≤ (x.2.2.look (x.1+i) (0,(0,0))).1) :
    volumeSum k x + 2 ≤ 2 * (prefixTable k x).len := by
  induction k generalizing x with
  | zero => simp [volumeSum,prefixTable,Tape.tab]
  | succ k ih =>
    have first : 2 ≤ (readRow x).1 := by simpa [readRow] using h 0 (by omega)
    have tail : ∀ i < k, 2 ≤ ((successor x).2.2.look
        ((successor x).1+i) (0,(0,0))).1 := by
      intro i hi
      simpa only [successor,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        h (i+1) (by omega)
    have small := ih (successor x) tail
    change volumeSum k (successor x) +
      (readRow x).1 * (prefixTable k (successor x)).len + 2 ≤
      2 * ((readRow x).1 * (prefixTable k (successor x)).len)
    nlinarith

/-- Pure Cartesian reference, in the same suffix-first order as the program. -/
def cartesian (V : ℕ) : (rs : List ℕ) →
    (Fin rs.length → ℕ) → (Fin rs.length → ℕ) → Tape (ℕ × ℕ)
  | [], _, _ => Tape.tab 1 (fun _ => (0,0))
  | r::rs, wa, wb =>
      let t := cartesian V rs (fun i => wa i.succ) (fun i => wb i.succ)
      Tape.tab (r*rs.prod) (fun j =>
        (((t.look (j%rs.prod) (0,0)).1+(j/rs.prod)*wa 0)%V,
         ((t.look (j%rs.prod) (0,0)).2+(j/rs.prod)*wb 0)%V))

@[simp] theorem cartesian_length (V : ℕ) (rs : List ℕ)
    (wa wb : Fin rs.length → ℕ) : (cartesian V rs wa wb).len = rs.prod := by
  cases rs <;> rfl

/-- The table enumerates physical MSB digits, with the last axis varying fastest. -/
theorem cartesian_coordinate (V : ℕ) (rs : List ℕ)
    (positive : ∀ r ∈ rs, 0 < r) (wa wb : Fin rs.length → ℕ)
    (ds : ∀ i : Fin rs.length, Fin (rs.get i)) :
    (cartesian V rs wa wb).look (listCoordinate rs ds).val (0,0) =
      ((∑ i, (ds i).val * wa i)%V, (∑ i, (ds i).val * wb i)%V) := by
  induction rs with
  | nil => simp [cartesian,listCoordinate,digitsEquiv,undigits,Tape.look,Tape.tab]
  | cons r rs ih =>
    have tp : 0 < rs.prod := List.prod_pos (fun q h => positive q (List.mem_cons_of_mem r h))
    have tailPositive : ∀ q ∈ rs, 0 < q := fun q h => positive q (List.mem_cons_of_mem r h)
    let z := listCoordinate rs (fun i => ds i.succ)
    have zv : z.val < rs.prod := z.isLt
    have coord : (listCoordinate (r::rs) ds).val = z.val+rs.prod*(ds 0).val := rfl
    have modEq : (z.val+rs.prod*(ds 0).val)%rs.prod = z.val := by
      rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt zv]
    have divEq : (z.val+rs.prod*(ds 0).val)/rs.prod = (ds 0).val := by
      rw [Nat.add_mul_div_left _ _ tp,Nat.div_eq_of_lt zv,Nat.zero_add]
    have lookup := ih tailPositive (fun i => wa i.succ) (fun i => wb i.succ)
      (fun i => ds i.succ)
    change _ = ((∑ i : Fin (rs.length+1), (ds i).val * wa i)%V,
      (∑ i : Fin (rs.length+1), (ds i).val * wb i)%V)
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    rw [Tape.look_of_lt _ _ (by simpa only [cartesian_length] using
      (listCoordinate (r::rs) ds).isLt)]
    change
      ((((cartesian V rs (fun i => wa i.succ) (fun i => wb i.succ)).look
        ((listCoordinate (r::rs) ds).val%rs.prod) (0,0)).1+
        ((listCoordinate (r::rs) ds).val/rs.prod)*wa 0)%V,
       (((cartesian V rs (fun i => wa i.succ) (fun i => wb i.succ)).look
        ((listCoordinate (r::rs) ds).val%rs.prod) (0,0)).2+
        ((listCoordinate (r::rs) ds).val/rs.prod)*wb 0)%V) = _
    rw [coord,modEq,divEq]
    change
      ((((cartesian V rs (fun i => wa i.succ) (fun i => wb i.succ)).look
        (listCoordinate rs (fun i => ds i.succ)).val (0,0)).1+(ds 0).val*wa 0)%V,
       (((cartesian V rs (fun i => wa i.succ) (fun i => wb i.succ)).look
        (listCoordinate rs (fun i => ds i.succ)).val (0,0)).2+(ds 0).val*wb 0)%V) = _
    rw [lookup]
    simp only [Nat.add_mod,Nat.mod_mod,Nat.add_comm]


/-- Exact row reads connect the executable suffix recursion to the Cartesian reference. -/
theorem prefix_cartesian (V : ℕ) (rs : List ℕ) (wa wb : Fin rs.length → ℕ)
    (x : Args.T) (volumeEq : x.2.1 = V)
    (rows : ∀ i : Fin rs.length, x.2.2.look (x.1+i.val) (0,(0,0)) =
      (rs.get i,(wa i,wb i))) :
    prefixTable rs.length x = cartesian V rs wa wb := by
  induction rs generalizing x with
  | nil => rfl
  | cons r rs ih =>
    have first : readRow x = (r,(wa 0,wb 0)) := by
      simpa [readRow] using rows 0
    have tail : ∀ i : Fin rs.length,
        (successor x).2.2.look ((successor x).1+i.val) (0,(0,0)) =
          (rs.get i,(wa i.succ,wb i.succ)) := by
      intro i
      simpa only [successor,Fin.val_succ,List.get_eq_getElem,
        List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rows i.succ
    change enlarged x (prefixTable rs.length (successor x)) = _
    rw [ih (fun i => wa i.succ) (fun i => wb i.succ) (successor x) volumeEq tail]
    unfold enlarged valueCell
    rw [first,cartesian_length,volumeEq]
    rfl

/-- Lookup by an ordinal is the weighted sum of its genuine physical digits. -/
theorem cartesian_digit (V : ℕ) (rs : List ℕ) (positive : ∀ r ∈ rs, 0 < r)
    (wa wb : Fin rs.length → ℕ) (p : Fin rs.prod) :
    (cartesian V rs wa wb).look p.val (0,0) =
      ((∑ i, ((p.val/(rs.drop (i.val+1)).prod)%rs.get i)*wa i)%V,
       (∑ i, ((p.val/(rs.drop (i.val+1)).prod)%rs.get i)*wb i)%V) := by
  let ds := (listCoordinate rs).symm p
  have atCoordinate := cartesian_coordinate V rs positive wa wb ds
  have coord : listCoordinate rs ds = p := Equiv.apply_symm_apply _ p
  rw [coord] at atCoordinate
  rw [atCoordinate]
  have digits : ∀ i : Fin rs.length,
      (p.val/(rs.drop (i.val+1)).prod)%rs.get i = (ds i).val := by
    intro i
    have h := UniformPhysicalCRTCoordinates.list_digit rs positive ds i
    rw [coord] at h
    exact h
  simp only [digits]


/-- Cartesian construction specialized to a finite radix family. -/
def finiteCartesian {a : ℕ} (V : ℕ) (r : Fin a → ℕ) (wa wb : Fin a → ℕ) :
    Tape (ℕ × ℕ) :=
  cartesian V (List.ofFn r) (fun i => wa (index r i)) (fun i => wb (index r i))

@[simp] theorem finiteCartesian_length {a : ℕ} (V : ℕ) (r : Fin a → ℕ)
    (wa wb : Fin a → ℕ) : (finiteCartesian V r wa wb).len = ∏ i, r i := by
  simp [finiteCartesian,List.prod_ofFn]

theorem finiteCartesian_coordinate {a : ℕ} (V : ℕ) (r : Fin a → ℕ)
    (hr : ∀ i, 0 < r i) (wa wb : Fin a → ℕ) (ds : ∀ i, Fin (r i)) :
    (finiteCartesian V r wa wb).look (physical r ds).val (0,0) =
      (UniformCRTTraversalCycle.weightedAddress V wa (fun i => (ds i).val),
       UniformCRTTraversalCycle.weightedAddress V wb (fun i => (ds i).val)) := by
  let f := (Equiv.piCongr (index r) (fun i => finCongr (shape r i))).symm ds
  have positive : ∀ q ∈ List.ofFn r, 0 < q := by
    intro q h
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
    exact hr i
  have h := cartesian_coordinate V (List.ofFn r) positive
    (fun i => wa (index r i)) (fun i => wb (index r i)) f
  change (cartesian V (List.ofFn r) (fun i => wa (index r i))
    (fun i => wb (index r i))).look (listCoordinate (List.ofFn r) f).val (0,0) = _
  rw [h]
  have sumEq (w : Fin a → ℕ) :
      (∑ i, (f i).val * w (index r i)) = ∑ i, w i * (ds i).val := by
    dsimp only [f]
    simp only [Equiv.piCongr_symm_apply,castval]
    exact Fintype.sum_equiv (index r) _ _ (fun i => Nat.mul_comm _ _)
  rw [sumEq wa,sumEq wb]
  rfl

/-- The ordinal-indexed cells use physical MSB digits, never normal LSB digits. -/
theorem finiteCartesian_digit {a : ℕ} (V : ℕ) (r : Fin a → ℕ)
    (hr : ∀ i, 0 < r i) (wa wb : Fin a → ℕ) (p : Fin (∏ i, r i)) :
    (finiteCartesian V r wa wb).look p.val (0,0) =
      (UniformCRTTraversalCycle.weightedAddress V wa (UniformPhysicalCRTArithmetic.digit r p.val),
       UniformCRTTraversalCycle.weightedAddress V wb (UniformPhysicalCRTArithmetic.digit r p.val)) := by
  let ds := (physical r).symm p
  have h := finiteCartesian_coordinate V r hr wa wb ds
  have coord : physical r ds = p := Equiv.apply_symm_apply _ p
  rw [coord] at h
  have digits : UniformPhysicalCRTArithmetic.digit r p.val = fun i => (ds i).val := by
    funext i
    have d := UniformPhysicalCRTCoordinates.physical_digit r hr ds i
    rw [coord] at d
    exact d
  rw [digits]
  exact h

/-- Exact ordinary row reads suffice to identify the actual recursion output. -/
theorem prefix_finiteCartesian {a : ℕ} (V : ℕ) (r : Fin a → ℕ)
    (wa wb : Fin a → ℕ) (x : Args.T) (volumeEq : x.2.1 = V)
    (rows : ∀ i : Fin a, x.2.2.look (x.1+i.val) (0,(0,0)) =
      (r i,(wa i,wb i))) :
    prefixTable a x = finiteCartesian V r wa wb := by
  have h := prefix_cartesian V (List.ofFn r)
    (fun i => wa (index r i)) (fun i => wb (index r i)) x volumeEq (fun i => ?_)
  · simpa only [List.length_ofFn,finiteCartesian] using h
  · rw [shape]
    exact rows (index r i)

end
end ExactFourierCircuits.DFTModelCRT

import UniformRoots
import OAI.Computability.FourierCircuit.ToeplitzCross
import Mathlib.Data.Nat.GCD.BigOperators

set_option autoImplicit false

/- Explicit integer CRT tables and their standard-root phase. The tables are
   computable; ring equivalences below only certify their meaning. Their charged
   preparation and array traversal have not yet been lowered to the RAM. -/
namespace ExactFourierCircuits.UniformCRT
open scoped BigOperators
open OAI.ExactFourier

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def cofactor (r : ι → ℕ) (i : ι) : ℕ := ∏ j ∈ Finset.univ.erase i, r j
def inverseDigit (r : ι → ℕ) (i : ι) : ℕ := ((cofactor r i : ZMod (r i))⁻¹).val
def idempotent (r : ι → ℕ) (i : ι) : ℕ := cofactor r i * inverseDigit r i
def address (r : ι → ℕ) (digits : ∀ i, Fin (r i)) : ℕ :=
  (∑ i, idempotent r i * (digits i).val) % (∏ i, r i)
def localOutput (r : ι → ℕ) (i : ι) (digit : ℕ) : ℕ := inverseDigit r i * digit % r i

theorem cofactor_mul (r : ι → ℕ) (i : ι) : cofactor r i * r i = ∏ j, r j :=
  Finset.prod_erase_mul _ _ (Finset.mem_univ i)

theorem cofactor_eq_div (r : ι → ℕ) (i : ι) (hi : 0 < r i) :
    cofactor r i = (∏ j, r j) / r i := by
  rw [← cofactor_mul r i, Nat.mul_div_cancel _ hi]

theorem cofactor_coprime (r : ι → ℕ)
    (hc : Pairwise (fun i j => Nat.Coprime (r i) (r j))) (i : ι) :
    Nat.Coprime (cofactor r i) (r i) := by
  apply Nat.coprime_prod_left_iff.mpr
  intro j hj
  exact hc (Finset.mem_erase.mp hj).1

theorem inverseDigit_lt (r : ι → ℕ) (i : ι) (hi : 0 < r i) : inverseDigit r i < r i := by
  let : NeZero (r i) := ⟨hi.ne'⟩
  exact ZMod.val_lt _

theorem idempotent_lt (r : ι → ℕ) (hr : ∀ i, 0 < r i) (i : ι) :
    idempotent r i < ∏ j, r j := by
  have hco : 0 < cofactor r i := Finset.prod_pos (fun j _ => hr j)
  rw [idempotent, ← cofactor_mul r i]
  exact Nat.mul_lt_mul_of_pos_left (inverseDigit_lt r i (hr i)) hco

theorem idempotent_self (r : ι → ℕ)
    (hc : Pairwise (fun i j => Nat.Coprime (r i) (r j))) (i : ι) :
    (idempotent r i : ZMod (r i)) = 1 := by
  simpa [idempotent, inverseDigit, Nat.cast_mul] using
    ZMod.mul_val_inv (cofactor_coprime r hc i)

theorem idempotent_other (r : ι → ℕ) (i j : ι) (hij : j ≠ i) :
    (idempotent r i : ZMod (r j)) = 0 := by
  have hd : r j ∣ cofactor r i := Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩)
  rw [idempotent, Nat.cast_mul, (ZMod.natCast_eq_zero_iff _ _).mpr hd, zero_mul]

theorem localOutput_inverse (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hc : Pairwise (fun i j => Nat.Coprime (r i) (r j))) (i : ι) (a : Fin (r i)) :
    cofactor r i * localOutput r i a.val % r i = a.val := by
  let : NeZero (r i) := ⟨(hr i).ne'⟩
  have hi : (cofactor r i : ZMod (r i)) * inverseDigit r i = 1 := by
    simpa [idempotent, Nat.cast_mul] using idempotent_self r hc i
  have he : ((cofactor r i * localOutput r i a.val : ℕ) : ZMod (r i)) = a.val := by
    simp only [localOutput, Nat.cast_mul, ZMod.natCast_mod]
    rw [← mul_assoc, hi, one_mul]
  have hv := congrArg ZMod.val he
  simpa [ZMod.val_mul, ZMod.val_natCast, Nat.mul_mod, Nat.mod_eq_of_lt a.isLt] using hv

theorem inverse_localOutput (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hc : Pairwise (fun i j => Nat.Coprime (r i) (r j))) (i : ι) (a : Fin (r i)) :
    localOutput r i (cofactor r i * a.val % r i) = a.val := by
  let : NeZero (r i) := ⟨(hr i).ne'⟩
  have hi : (inverseDigit r i : ZMod (r i)) * cofactor r i = 1 := by
    simpa [idempotent, Nat.cast_mul, mul_comm] using idempotent_self r hc i
  have he : ((inverseDigit r i * (cofactor r i * a.val % r i) : ℕ) : ZMod (r i)) = a.val := by
    simp only [Nat.cast_mul, ZMod.natCast_mod]
    rw [← mul_assoc, hi, one_mul]
  have hv := congrArg ZMod.val he
  simpa [localOutput, ZMod.val_mul, ZMod.val_natCast, Nat.mul_mod, Nat.mod_eq_of_lt a.isLt] using hv

def localPermutation (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hc : Pairwise (fun i j => Nat.Coprime (r i) (r j))) (i : ι) : Equiv.Perm (Fin (r i)) where
  toFun a := ⟨localOutput r i a.val, Nat.mod_lt _ (hr i)⟩
  invFun a := ⟨cofactor r i * a.val % r i, Nat.mod_lt _ (hr i)⟩
  left_inv a := Fin.ext (localOutput_inverse r hr hc i a)
  right_inv a := Fin.ext (inverse_localOutput r hr hc i a)

theorem idempotent_projection (r : ι → ℕ)
    (hc : Pairwise (fun i j => Nat.Coprime (r i) (r j))) (i : ι) :
    ZMod.prodEquivPi r hc (idempotent r i : ZMod (∏ j, r j)) = FourierCRT.singleAdd r i 1 := by
  funext j
  rw [ZMod.prodEquivPi_apply, ZMod.castHom_apply,
    ZMod.cast_natCast (Finset.dvd_prod_of_mem r (Finset.mem_univ j))]
  by_cases hji : j = i
  · subst j; simpa [FourierCRT.singleAdd] using idempotent_self r hc i
  · simpa [FourierCRT.singleAdd, hji] using idempotent_other r i j hji

noncomputable section

theorem component_specified_root (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hc : Pairwise (fun i j => Nat.Coprime (r i) (r j))) (i : ι) :
    letI : NeZero (∏ j, r j) := ⟨(Finset.prod_pos (fun j _ => hr j)).ne'⟩
    FourierCRT.component r hc i 1 = zeta (r i) ^ inverseDigit r i := by
  let : NeZero (∏ j, r j) := ⟨(Finset.prod_pos (fun j _ => hr j)).ne'⟩
  have he : (ZMod.prodEquivPi r hc).symm (FourierCRT.singleAdd r i 1) =
      (idempotent r i : ZMod (∏ j, r j)) := by
    rw [← idempotent_projection r hc i, RingEquiv.symm_apply_apply]
  change ZMod.stdAddChar ((ZMod.prodEquivPi r hc).symm (FourierCRT.singleAdd r i 1)) = _
  rw [he, FourierCRT.char_nat, FourierCRT.standard_root, idempotent, pow_mul,
    cofactor_eq_div r i (hr i)]
  rw [UniformRoots.specifiedRoot_divisor_power _ _ (Finset.prod_pos (fun j _ => hr j))
    (hr i) (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))]

theorem local_root_primitive (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hc : Pairwise (fun i j => Nat.Coprime (r i) (r j))) (i : ι) :
    IsPrimitiveRoot (zeta (r i) ^ inverseDigit r i) (r i) := by
  let : NeZero (∏ j, r j) := ⟨(Finset.prod_pos (fun j _ => hr j)).ne'⟩
  rw [← component_specified_root r hr hc i]
  exact FourierCRT.root_primitive _ (FourierCRT.component_injective r hc i)

theorem crt_sum (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hc : Pairwise (fun i j => Nat.Coprime (r i) (r j))) (digits : ∀ i, ZMod (r i)) :
    (ZMod.prodEquivPi r hc).symm digits =
      ∑ i, (idempotent r i : ZMod (∏ j, r j)) * (digits i).val := by
  let : ∀ i, NeZero (r i) := fun i => ⟨(hr i).ne'⟩
  apply (ZMod.prodEquivPi r hc).injective
  rw [RingEquiv.apply_symm_apply, map_sum]
  have hterm (i : ι) :
      ZMod.prodEquivPi r hc ((idempotent r i : ZMod (∏ j, r j)) * (digits i).val) =
        FourierCRT.singleAdd r i (digits i) := by
    rw [map_mul, idempotent_projection]
    funext j
    by_cases hji : j = i
    · subst j
      simp [FourierCRT.singleAdd]
    · simp [FourierCRT.singleAdd, hji]
  simp_rw [hterm]
  exact (FourierCRT.sum_singleAdd r digits).symm

theorem address_lt (r : ι → ℕ) (hr : ∀ i, 0 < r i) (digits : ∀ i, Fin (r i)) :
    address r digits < ∏ i, r i :=
  Nat.mod_lt _ (Finset.prod_pos (fun i _ => hr i))

theorem address_crt (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hc : Pairwise (fun i j => Nat.Coprime (r i) (r j))) (digits : ∀ i, Fin (r i)) :
    letI : NeZero (∏ i, r i) := ⟨(Finset.prod_pos (fun j _ => hr j)).ne'⟩
    (address r digits : ZMod (∏ i, r i)) =
      (ZMod.prodEquivPi r hc).symm (fun i => ((digits i).val : ZMod (r i))) := by
  let : ∀ i, NeZero (r i) := fun i => ⟨(hr i).ne'⟩
  let : NeZero (∏ i, r i) := ⟨(Finset.prod_pos (fun j _ => hr j)).ne'⟩
  rw [crt_sum r hr, address, ZMod.natCast_mod, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_mul, ZMod.val_natCast, Nat.mod_eq_of_lt (digits i).isLt]

end

def decode (r : ι → ℕ) (hr : ∀ i, 0 < r i) (j : Fin (∏ i, r i)) : ∀ i, Fin (r i) :=
  fun i => ⟨j.val % r i, Nat.mod_lt _ (hr i)⟩

def encode (r : ι → ℕ) (hr : ∀ i, 0 < r i) (digits : ∀ i, Fin (r i)) : Fin (∏ i, r i) :=
  ⟨address r digits, address_lt r hr digits⟩

theorem decode_encode (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hc : Pairwise (fun i j => Nat.Coprime (r i) (r j))) (digits : ∀ i, Fin (r i)) :
    decode r hr (encode r hr digits) = digits := by
  let : ∀ i, NeZero (r i) := fun i => ⟨(hr i).ne'⟩
  let : NeZero (∏ i, r i) := ⟨(Finset.prod_pos (fun j _ => hr j)).ne'⟩
  funext i
  apply Fin.ext
  have he := congrFun (congrArg (ZMod.prodEquivPi r hc) (address_crt r hr hc digits)) i
  rw [RingEquiv.apply_symm_apply, ZMod.prodEquivPi_apply, ZMod.castHom_apply,
    ZMod.cast_natCast (Finset.dvd_prod_of_mem r (Finset.mem_univ i))] at he
  have hv := congrArg ZMod.val he
  simpa [decode, encode, ZMod.val_natCast, Nat.mod_eq_of_lt (digits i).isLt] using hv

theorem encode_decode (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hc : Pairwise (fun i j => Nat.Coprime (r i) (r j))) (j : Fin (∏ i, r i)) :
    encode r hr (decode r hr j) = j := by
  let : ∀ i, NeZero (r i) := fun i => ⟨(hr i).ne'⟩
  let : NeZero (∏ i, r i) := ⟨(Finset.prod_pos (fun j _ => hr j)).ne'⟩
  have hd : (fun i => ((decode r hr j i).val : ZMod (r i))) =
      ZMod.prodEquivPi r hc (j.val : ZMod (∏ i, r i)) := by
    funext i
    rw [ZMod.prodEquivPi_apply, ZMod.castHom_apply,
      ZMod.cast_natCast (Finset.dvd_prod_of_mem r (Finset.mem_univ i))]
    simp [decode]
  have he := address_crt r hr hc (decode r hr j)
  rw [hd, RingEquiv.symm_apply_apply] at he
  have hv := congrArg ZMod.val he
  apply Fin.ext
  simpa [encode, ZMod.val_natCast, Nat.mod_eq_of_lt (address_lt r hr _),
    Nat.mod_eq_of_lt j.isLt] using hv

/-- The permutation is computed by the printed idempotent sum, with residue decoding. -/
def permutation (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hc : Pairwise (fun i j => Nat.Coprime (r i) (r j))) :
    (∀ i, Fin (r i)) ≃ Fin (∏ i, r i) where
  toFun := encode r hr
  invFun := decode r hr
  left_inv := decode_encode r hr hc
  right_inv := encode_decode r hr hc

noncomputable section

theorem fourier_phase (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hc : Pairwise (fun i j => Nat.Coprime (r i) (r j)))
    (j k : ∀ i, Fin (r i)) :
    zeta (∏ i, r i) ^ ((encode r hr j).val * (encode r hr k).val) =
      ∏ i, zeta (r i) ^ (inverseDigit r i * (j i).val * (k i).val) := by
  let : ∀ i, NeZero (r i) := fun i => ⟨(hr i).ne'⟩
  let : NeZero (∏ i, r i) := ⟨(Finset.prod_pos (fun j _ => hr j)).ne'⟩
  have hj : ZMod.prodEquivPi r hc ((encode r hr j).val : ZMod (∏ i, r i)) =
      fun i => ((j i).val : ZMod (r i)) := by
    change ZMod.prodEquivPi r hc (address r j : ZMod (∏ i, r i)) = _
    rw [address_crt r hr hc, RingEquiv.apply_symm_apply]
  have hk : ZMod.prodEquivPi r hc ((encode r hr k).val : ZMod (∏ i, r i)) =
      fun i => ((k i).val : ZMod (r i)) := by
    change ZMod.prodEquivPi r hc (address r k : ZMod (∏ i, r i)) = _
    rw [address_crt r hr hc, RingEquiv.apply_symm_apply]
  have hp : ZMod.prodEquivPi r hc (((encode r hr j).val * (encode r hr k).val : ℕ) :
      ZMod (∏ i, r i)) = fun i => (((j i).val * (k i).val : ℕ) : ZMod (r i)) := by
    rw [Nat.cast_mul, map_mul, hj, hk]
    funext i
    simp
  have he := FourierCRT.character_factor r hc
    (fun i => (((j i).val * (k i).val : ℕ) : ZMod (r i)))
  rw [← hp, RingEquiv.symm_apply_apply, FourierCRT.char_nat, FourierCRT.standard_root] at he
  rw [he]
  apply Finset.prod_congr rfl
  intro i _
  rw [FourierCRT.char_nat, component_specified_root r hr hc i, ← pow_mul, Nat.mul_assoc]

/-- Exact tensor factorization with computed indices and specified local phases. -/
theorem matrix_factorization (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hc : Pairwise (fun i j => Nat.Coprime (r i) (r j))) :
    Matrix.reindex (permutation r hr hc).symm (permutation r hr hc).symm
      (fourierMatrix (∏ i, r i)) =
        PiTensor.matrix (fun i => RadixTwo.dft (r i) (zeta (r i) ^ inverseDigit r i)) := by
  ext j k
  change zeta (∏ i, r i) ^ ((encode r hr j).val * (encode r hr k).val) =
    ∏ i, (zeta (r i) ^ inverseDigit r i) ^ ((j i).val * (k i).val)
  rw [fourier_phase r hr hc]
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_mul, Nat.mul_assoc]

end
end ExactFourierCircuits.UniformCRT

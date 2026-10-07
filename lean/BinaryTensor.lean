import BinaryFrames
import Mathlib

set_option autoImplicit false

/- Symbolic binary tensor and weight identities used by the signed frame construction. -/
namespace ExactFourierCircuits.BinaryTensor

open scoped BigOperators
open BinaryFrames
noncomputable section

/-- The integer representative 0 or 1 of a binary scalar. -/
def bit (a : F2) : ℕ := a.val

@[simp] theorem bit_zero : bit (0 : F2) = 0 := by norm_num [bit]
@[simp] theorem bit_one : bit (1 : F2) = 1 := rfl
@[simp] theorem bit_cast (a : F2) : (bit a : F2) = a := ZMod.natCast_zmod_val a

theorem bit_mul (a b : F2) : bit (a * b) = bit a * bit b := by
  fin_cases a <;> fin_cases b <;> decide

theorem bit_sq (a : F2) : bit a * bit a = bit a := by
  fin_cases a <;> decide

theorem bit_add_overlap (a b : F2) :
    bit (a + b) + 2 * (bit a * bit b) = bit a + bit b := by
  fin_cases a <;> fin_cases b <;> decide

theorem bit_finset_prod {μ : Type*} (s : Finset μ) (c : μ → F2) :
    bit (∏ i ∈ s, c i) = ∏ i ∈ s, bit (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, bit_mul, ih]

variable {ι η κ α : Type*} [Fintype ι] [Fintype η]

def weight (x : Vec ι) : ℕ := ∑ i, bit (x i)
def overlap (x y : Vec ι) : ℕ := ∑ i, bit (x i) * bit (y i)
def weightModFour (x : Vec ι) : ZMod 4 := weight x

@[simp] theorem weight_zero : weight (0 : Vec ι) = 0 := by simp [weight]
@[simp] theorem weightModFour_zero : weightModFour (0 : Vec ι) = 0 := by
  simp [weightModFour]

/-- Weight counts support, rather than a chosen coordinate encoding. -/
theorem weight_eq_support_card (x : Vec ι) :
    weight x = (Finset.univ.filter (fun i => x i ≠ 0)).card := by
  classical
  have hb (a : F2) : bit a = if a ≠ 0 then 1 else 0 := by
    fin_cases a <;> decide
  simp only [weight, hb]
  simp [Finset.card_filter]

theorem overlap_cast (x y : Vec ι) : (overlap x y : F2) = dot x y := by
  simp [overlap, dot, Nat.cast_sum, Nat.cast_mul]

theorem weight_cast_norm (x : Vec ι) : (weight x : F2) = dot x x := by
  rw [← overlap_cast]
  congr 1
  simp [weight, overlap, bit_sq]

/-- The natural-number form avoids any use of truncated subtraction. -/
theorem weight_add_overlap (x y : Vec ι) :
    weight (x + y) + 2 * overlap x y = weight x + weight y := by
  simp only [weight, overlap, Pi.add_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => bit_add_overlap (x i) (y i))

theorem overlap_even_of_dot_zero (x y : Vec ι) (hxy : dot x y = 0) :
    2 ∣ overlap x y := by
  apply (ZMod.natCast_eq_zero_iff (overlap x y) 2).mp
  rw [overlap_cast, hxy]

theorem weightModFour_add_of_dot_zero (x y : Vec ι) (hxy : dot x y = 0) :
    weightModFour (x + y) = weightModFour x + weightModFour y := by
  obtain ⟨k, hk⟩ := overlap_even_of_dot_zero x y hxy
  have h := congrArg (fun n : ℕ => (n : ZMod 4)) (weight_add_overlap x y)
  simp only [Nat.cast_add, Nat.cast_mul] at h
  have hz : (2 : ZMod 4) * (overlap x y : ZMod 4) = 0 := by
    rw [hk, Nat.cast_mul, ← mul_assoc]
    norm_num
    rw [show (4 : ZMod 4) = 0 from ZMod.natCast_self 4, zero_mul]
  norm_num only [Nat.cast_ofNat] at h
  simpa only [weightModFour, hz, add_zero] using h

theorem weightModFour_smul (c : F2) (x : Vec ι) :
    weightModFour (c • x) = (bit c : ZMod 4) * weightModFour x := by
  have hc : c = 0 ∨ c = 1 := by
    fin_cases c
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hc with rfl | rfl <;> simp

theorem norm_one_weight_mod_four (x : Vec ι) (hx : dot x x = 1) :
    weight x % 4 = 1 ∨ weight x % 4 = 3 := by
  have h : weight x % 2 = 1 := by
    have hcast : (weight x : F2) = 1 := (weight_cast_norm x).trans hx
    have hval := congrArg ZMod.val hcast
    simpa only [ZMod.val_natCast, ZMod.val_one] using hval
  omega

/-- Ordinary binary tensor coordinates: the right factor is the inner coordinate. -/
def tensor (x : Vec ι) (y : Vec η) : Vec (ι × η) := fun ij => x ij.1 * y ij.2

theorem dot_tensor (x x' : Vec ι) (y y' : Vec η) :
    dot (tensor x y) (tensor x' y') = dot x x' * dot y y' := by
  simp only [dot, tensor, Fintype.sum_prod_type]
  calc
    _ = ∑ i, ∑ j, (x i * x' i) * (y j * y' j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by simp_rw [← Finset.mul_sum]; rw [← Finset.sum_mul]

theorem weight_tensor (x : Vec ι) (y : Vec η) :
    weight (tensor x y) = weight x * weight y := by
  simp only [weight, tensor, Fintype.sum_prod_type, bit_mul]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

theorem tensor_norm_one (x : Vec ι) (y : Vec η)
    (hx : dot x x = 1) (hy : dot y y = 1) :
    dot (tensor x y) (tensor x y) = 1 := by
  rw [dot_tensor, hx, hy, mul_one]

theorem tensor_orthonormal (x : κ → Vec ι) (y : α → Vec η)
    [DecidableEq κ] [DecidableEq α]
    (hx : ∀ i j, dot (x i) (x j) = if i = j then 1 else 0)
    (hy : ∀ i j, dot (y i) (y j) = if i = j then 1 else 0)
    (p q : κ × α) :
    dot (tensor (x p.1) (y p.2)) (tensor (x q.1) (y q.2)) =
      if p = q then 1 else 0 := by
  rw [dot_tensor, hx, hy]
  by_cases h₁ : p.1 = q.1 <;> by_cases h₂ : p.2 = q.2 <;>
    simp [h₁, h₂, Prod.ext_iff]

/-- The empty tensor is the unit in a one-coordinate binary space, not a zero vector. -/
def emptyTensor : Vec PUnit := fun _ => 1

@[simp] theorem emptyTensor_weight : weight emptyTensor = 1 := by
  simp [weight, emptyTensor]

@[simp] theorem emptyTensor_norm : dot emptyTensor emptyTensor = 1 := by
  simp [dot, emptyTensor]

section FiniteTensor
variable {μ : Type*} [Fintype μ] [DecidableEq μ]
  {δ : μ → Type*} [∀ i, Fintype (δ i)]

/-- A tensor over any finite family, including an empty family of factors. -/
def tensorFamily (x : ∀ i, Vec (δ i)) : Vec (∀ i, δ i) := by
  classical
  exact fun p => ∏ i, x i (p i)

theorem dot_tensorFamily (x y : ∀ i, Vec (δ i)) :
    dot (tensorFamily x) (tensorFamily y) = ∏ i, dot (x i) (y i) := by
  classical
  simp only [dot, tensorFamily, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i j => x i j * y i j)).symm

theorem weight_tensorFamily (x : ∀ i, Vec (δ i)) :
    weight (tensorFamily x) = ∏ i, weight (x i) := by
  classical
  simp only [weight, tensorFamily, bit_finset_prod]
  exact (Fintype.prod_sum (fun i j => bit (x i j))).symm

theorem tensorFamily_norm_one (x : ∀ i, Vec (δ i))
    (hx : ∀ i, dot (x i) (x i) = 1) :
    dot (tensorFamily x) (tensorFamily x) = 1 := by
  rw [dot_tensorFamily]
  simp [hx]

theorem tensorFamily_empty_weight [IsEmpty μ] (x : ∀ i, Vec (δ i)) :
    weight (tensorFamily x) = 1 := by
  rw [weight_tensorFamily]
  simp

theorem tensorFamily_empty_norm [IsEmpty μ] (x : ∀ i, Vec (δ i)) :
    dot (tensorFamily x) (tensorFamily x) = 1 := by
  rw [dot_tensorFamily]
  simp

end FiniteTensor

theorem dot_finset_sum_right (x : Vec ι) (s : Finset κ) (z : κ → Vec ι) :
    dot x (∑ j ∈ s, z j) = ∑ j ∈ s, dot x (z j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dot]
  | @insert a s ha ih => simp [ha, dot_add_right, ih]

/-- Signed-phase exponent decomposition. Norm-one is not needed for additivity;
    it is needed separately to replace each coefficient by +1 or -1 modulo four. -/
theorem orthogonal_sum_weightModFour (s : Finset κ) (z : κ → Vec ι) (c : κ → F2)
    (horth : ∀ i j, i ≠ j → dot (z i) (z j) = 0) :
    weightModFour (∑ i ∈ s, c i • z i) =
      ∑ i ∈ s, (bit (c i) : ZMod 4) * weightModFour (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hd : dot (c a • z a) (∑ j ∈ s, c j • z j) = 0 := by
      rw [dot_smul_left, dot_finset_sum_right]
      have hz : (∑ j ∈ s, dot (z a) (c j • z j)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [dot_smul_right, horth a j (by intro h; subst j; exact ha hj), mul_zero]
      rw [hz, mul_zero]
    rw [Finset.sum_insert ha, weightModFour_add_of_dot_zero _ _ hd,
      weightModFour_smul, ih, Finset.sum_insert ha]

theorem orthogonal_family_weightModFour [Fintype κ] (z : κ → Vec ι) (c : κ → F2)
    (horth : ∀ i j, i ≠ j → dot (z i) (z j) = 0) :
    weightModFour (∑ i, c i • z i) =
      ∑ i, (bit (c i) : ZMod 4) * weightModFour (z i) :=
  orthogonal_sum_weightModFour Finset.univ z c horth

theorem orthogonal_sum_weight_mod_four (s : Finset κ) (z : κ → Vec ι) (c : κ → F2)
    (horth : ∀ i j, i ≠ j → dot (z i) (z j) = 0) :
    weight (∑ i ∈ s, c i • z i) % 4 =
      (∑ i ∈ s, bit (c i) * weight (z i)) % 4 := by
  have h := orthogonal_sum_weightModFour s z c horth
  have hc : (weight (∑ i ∈ s, c i • z i) : ZMod 4) =
      (∑ i ∈ s, bit (c i) * weight (z i) : ℕ) := by
    simpa [weightModFour, Nat.cast_sum, Nat.cast_mul] using h
  simpa only [ZMod.val_natCast] using congrArg ZMod.val hc

/-- Orthogonal projection onto the span when the frame is orthonormal. -/
def frameProjection [Fintype κ] (z : κ → Vec ι) (x : Vec ι) : Vec ι :=
  ∑ i, dot (z i) x • z i

theorem frameProjection_dot [Fintype κ] (z : κ → Vec ι) (x : Vec ι)
    (horth : ∀ i j, i ≠ j → dot (z i) (z j) = 0)
    (hunit : ∀ i, dot (z i) (z i) = 1) (j : κ) :
    dot (z j) (frameProjection z x) = dot (z j) x := by
  classical
  rw [frameProjection, dot_finset_sum_right]
  simp only [dot_smul_right]
  rw [Finset.sum_eq_single j]
  · rw [hunit j, mul_one]
  · intro i hi hij
    rw [horth j i (Ne.symm hij), mul_zero]
  · simp

theorem frameProjection_idempotent [Fintype κ] (z : κ → Vec ι) (x : Vec ι)
    (horth : ∀ i j, i ≠ j → dot (z i) (z j) = 0)
    (hunit : ∀ i, dot (z i) (z i) = 1) :
    frameProjection z (frameProjection z x) = frameProjection z x := by
  change (∑ i, dot (z i) (frameProjection z x) • z i) = ∑ i, dot (z i) x • z i
  simp only [frameProjection_dot z x horth hunit]

theorem frameProjection_weightModFour [Fintype κ] (z : κ → Vec ι) (x : Vec ι)
    (horth : ∀ i j, i ≠ j → dot (z i) (z j) = 0) :
    weightModFour (frameProjection z x) =
      ∑ i, (bit (dot (z i) x) : ZMod 4) * weightModFour (z i) :=
  orthogonal_family_weightModFour z (fun i => dot (z i) x) horth

end
end ExactFourierCircuits.BinaryTensor

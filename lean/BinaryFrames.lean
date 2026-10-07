import Mathlib
set_option autoImplicit false

/- Exact finite-index algebra for gf2.py's transvection complement construction.
   Pivot existence and the alternating-complement failure classification are not assumed proved. -/
namespace ExactFourierCircuits.BinaryFrames
open scoped BigOperators
noncomputable section

abbrev F2 := ZMod 2
abbrev Vec (ι : Type*) := ι → F2
variable {ι : Type*} [Fintype ι]

def dot (x y : Vec ι) : F2 := ∑ i, x i * y i

lemma dot_comm (x y : Vec ι) : dot x y = dot y x := by
  simp only [dot, mul_comm]

lemma dot_add_left (x y z : Vec ι) : dot (x + y) z = dot x z + dot y z := by
  simp [dot, add_mul, Finset.sum_add_distrib]

lemma dot_add_right (x y z : Vec ι) : dot x (y + z) = dot x y + dot x z := by
  simp [dot, mul_add, Finset.sum_add_distrib]

lemma dot_smul_left (c : F2) (x y : Vec ι) : dot (c • x) y = c * dot x y := by
  simp [dot, Finset.mul_sum, mul_assoc]

lemma dot_smul_right (c : F2) (x y : Vec ι) : dot x (c • y) = c * dot x y := by
  rw [dot_comm, dot_smul_left, dot_comm y x]

/-- The same update as sparse XOR by v when dot(v,x)=1. Linearity needs no norm hypothesis. -/
def transvection (v : Vec ι) : Vec ι →ₗ[F2] Vec ι where
  toFun x := x + dot v x • v
  map_add' x y := by
    rw [dot_add_right]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  map_smul' c x := by
    rw [dot_smul_right]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] lemma transvection_apply (v x : Vec ι) :
    transvection v x = x + dot v x • v := rfl

theorem transvection_add (v x y : Vec ι) :
    transvection v (x + y) = transvection v x + transvection v y :=
  (transvection v).map_add x y

theorem transvection_smul (v x : Vec ι) (c : F2) :
    transvection v (c • x) = c • transvection v x :=
  (transvection v).map_smul c x

theorem transvection_involutive (v : Vec ι) (hv : dot v v = 0) :
    Function.Involutive (transvection v) := by
  intro x
  simp only [transvection_apply, dot_add_right, dot_smul_right, hv, mul_zero, add_zero]
  ext i
  change x i + dot v x * v i + dot v x * v i = x i
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem transvection_preserves_dot (v : Vec ι) (hv : dot v v = 0) (x y : Vec ι) :
    dot (transvection v x) (transvection v y) = dot x y := by
  calc
    _ = dot x y + (dot v x * dot v y + dot v x * dot v y) := by
      simp only [transvection_apply, dot_add_left, dot_add_right,
        dot_smul_left, dot_smul_right, hv, mul_zero, add_zero]
      rw [dot_comm x v]
      ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]

lemma transvection_self_adjoint (v x y : Vec ι) :
    dot (transvection v x) y = dot x (transvection v y) := by
  simp only [transvection_apply, dot_add_left, dot_add_right, dot_smul_left, dot_smul_right]
  rw [dot_comm x v]
  ring

/-- Isotropic transvections are genuine linear equivalences, with themselves as inverse. -/
def transvectionEquiv (v : Vec ι) (hv : dot v v = 0) : Vec ι ≃ₗ[F2] Vec ι where
  toFun := transvection v
  invFun := transvection v
  left_inv := transvection_involutive v hv
  right_inv := transvection_involutive v hv
  map_add' := (transvection v).map_add
  map_smul' := (transvection v).map_smul

@[simp] lemma transvectionEquiv_apply (v : Vec ι) (hv : dot v v = 0) (x : Vec ι) :
    transvectionEquiv v hv x = transvection v x := rfl

variable [DecidableEq ι]

def unit (p : ι) : Vec ι := fun i => if i = p then 1 else 0

@[simp] lemma dot_unit_left (p : ι) (x : Vec ι) : dot (unit p) x = x p := by
  simp [dot, unit]

@[simp] lemma dot_unit_right (x : Vec ι) (p : ι) : dot x (unit p) = x p := by
  rw [dot_comm, dot_unit_left]

@[simp] lemma dot_units (p q : ι) : dot (unit p) (unit q) = if p = q then 1 else 0 := by
  simp [unit, eq_comm]

theorem pivot_direction_isotropic (u : Vec ι) (p : ι)
    (hu : dot u u = 1) (hp : u p = 0) : dot (unit p + u) (unit p + u) = 0 := by
  rw [dot_add_left, dot_add_right, dot_add_right]
  simp [hu, hp, unit, CharTwo.add_self_eq_zero]

theorem pivot_transvection_unit (u : Vec ι) (p : ι) (hp : u p = 0) :
    transvection (unit p + u) (unit p) = u := by
  simp only [transvection_apply, dot_unit_right]
  simp [unit, hp]
  ext i
  by_cases hi : i = p
  · subst i; simp [unit, hp, CharTwo.add_self_eq_zero]
  · simp [unit, hi]

def firstImage (u y : Vec ι) (p : ι) : Vec ι := transvection (unit p + u) y

def twoFrame (u y : Vec ι) (p q : ι) : Vec ι →ₗ[F2] Vec ι :=
  (transvection (unit p + u)).comp (transvection (unit q + firstImage u y p))

@[simp] lemma twoFrame_apply (u y x : Vec ι) (p q : ι) :
    twoFrame u y p q x = transvection (unit p + u)
      (transvection (unit q + firstImage u y p) x) := rfl

lemma firstImage_norm (u y : Vec ι) (p : ι) (hu : dot u u = 1)
    (hy : dot y y = 1) (hp : u p = 0) :
    dot (firstImage u y p) (firstImage u y p) = 1 := by
  exact (transvection_preserves_dot (unit p + u)
    (pivot_direction_isotropic u p hu hp) y y).trans hy

lemma firstImage_pivot_zero (u y : Vec ι) (p : ι)
    (huy : dot u y = 0) (hp : u p = 0) : firstImage u y p p = 0 := by
  rw [← dot_unit_left p (firstImage u y p)]
  change dot (unit p) (transvection (unit p + u) y) = 0
  rw [← transvection_self_adjoint, pivot_transvection_unit u p hp, huy]

/-- Exactly the Python order: apply second transvection, then first. -/
def twoFrameEquiv (u y : Vec ι) (p q : ι)
    (hu : dot u u = 1) (hy : dot y y = 1) (hp : u p = 0)
    (hq : firstImage u y p q = 0) : Vec ι ≃ₗ[F2] Vec ι :=
  (transvectionEquiv (unit q + firstImage u y p)
    (pivot_direction_isotropic _ q (firstImage_norm u y p hu hy hp) hq)).trans
      (transvectionEquiv (unit p + u) (pivot_direction_isotropic u p hu hp))

@[simp] lemma twoFrameEquiv_apply (u y x : Vec ι) (p q : ι)
    (hu : dot u u = 1) (hy : dot y y = 1) (hp : u p = 0)
    (hq : firstImage u y p q = 0) :
    twoFrameEquiv u y p q hu hy hp hq x = twoFrame u y p q x := rfl

theorem twoFrame_preserves_dot (u y : Vec ι) (p q : ι)
    (hu : dot u u = 1) (hy : dot y y = 1) (hp : u p = 0)
    (hq : firstImage u y p q = 0) (x z : Vec ι) :
    dot (twoFrame u y p q x) (twoFrame u y p q z) = dot x z := by
  rw [twoFrame_apply, twoFrame_apply,
    transvection_preserves_dot _ (pivot_direction_isotropic u p hu hp)]
  exact transvection_preserves_dot _
    (pivot_direction_isotropic _ q (firstImage_norm u y p hu hy hp) hq) x z

theorem twoFrame_unit_first (u y : Vec ι) (p q : ι)
    (huy : dot u y = 0) (hp : u p = 0) (hqp : q ≠ p) :
    twoFrame u y p q (unit p) = u := by
  have hw : firstImage u y p p = 0 := firstImage_pivot_zero u y p huy hp
  rw [twoFrame_apply]
  have hz : dot (unit q + firstImage u y p) (unit p) = 0 := by
    simp [unit, hw, Ne.symm hqp]
  have hs : transvection (unit q + firstImage u y p) (unit p) = unit p := by
    rw [transvection_apply, hz, zero_smul, add_zero]
  rw [hs, pivot_transvection_unit u p hp]

theorem twoFrame_unit_second (u y : Vec ι) (p q : ι)
    (hu : dot u u = 1) (hp : u p = 0) (hq : firstImage u y p q = 0) :
    twoFrame u y p q (unit q) = y := by
  rw [twoFrame_apply, pivot_transvection_unit _ q hq]
  exact transvection_involutive (unit p + u) (pivot_direction_isotropic u p hu hp) y

theorem twoFrame_orthonormal (u y : Vec ι) (p q : ι)
    (hu : dot u u = 1) (hy : dot y y = 1) (hp : u p = 0)
    (hq : firstImage u y p q = 0) (i j : ι) :
    dot (twoFrame u y p q (unit i)) (twoFrame u y p q (unit j)) =
      if i = j then 1 else 0 := by
  rw [twoFrame_preserves_dot u y p q hu hy hp hq, dot_units]

theorem twoFrame_complement_orthogonal (u y : Vec ι) (p q : ι)
    (hu : dot u u = 1) (hy : dot y y = 1) (huy : dot u y = 0)
    (hp : u p = 0) (hqp : q ≠ p) (hq : firstImage u y p q = 0)
    (j : ι) (hjp : j ≠ p) (hjq : j ≠ q) :
    dot u (twoFrame u y p q (unit j)) = 0 ∧
      dot y (twoFrame u y p q (unit j)) = 0 := by
  constructor
  · calc
      _ = dot (twoFrame u y p q (unit p)) (twoFrame u y p q (unit j)) := by
        rw [twoFrame_unit_first u y p q huy hp hqp]
      _ = dot (unit p) (unit j) := twoFrame_preserves_dot u y p q hu hy hp hq _ _
      _ = 0 := by simp [unit, hjp]
  · calc
      _ = dot (twoFrame u y p q (unit q)) (twoFrame u y p q (unit j)) := by
        rw [twoFrame_unit_second u y p q hu hp hq]
      _ = dot (unit q) (unit j) := twoFrame_preserves_dot u y p q hu hy hp hq _ _
      _ = 0 := by simp [unit, hjq]

lemma unit_decomposition (x : Vec ι) : (∑ i, x i • unit i) = x := by
  ext j
  simp [unit, Finset.sum_apply]

lemma frame_decomposition (u y x : Vec ι) (p q : ι) :
    (∑ i, x i • twoFrame u y p q (unit i)) = twoFrame u y p q x := by
  calc
    _ = twoFrame u y p q (∑ i, x i • unit i) := by
      simp only [map_sum, map_smul]
    _ = _ := by rw [unit_decomposition x]

/-- Complement images span every vector perpendicular to the two prescribed vectors. -/
theorem twoFrame_complement_spans (u y : Vec ι) (p q : ι)
    (hu : dot u u = 1) (hy : dot y y = 1) (huy : dot u y = 0)
    (hp : u p = 0) (hqp : q ≠ p) (hq : firstImage u y p q = 0)
    (x : Vec ι) (hux : dot u x = 0) (hyx : dot y x = 0) :
    ∃ c : Vec ι, c p = 0 ∧ c q = 0 ∧
      (∑ i ∈ Finset.univ.filter (fun i => i ≠ p ∧ i ≠ q),
        c i • twoFrame u y p q (unit i)) = x := by
  let E := twoFrameEquiv u y p q hu hy hp hq
  let c := E.symm x
  have hc : twoFrame u y p q c = x := E.apply_symm_apply x
  have hcp : c p = 0 := by
    have h := twoFrame_preserves_dot u y p q hu hy hp hq (unit p) c
    rw [twoFrame_unit_first u y p q huy hp hqp, hc, dot_unit_left, hux] at h
    exact h.symm
  have hcq : c q = 0 := by
    have h := twoFrame_preserves_dot u y p q hu hy hp hq (unit q) c
    rw [twoFrame_unit_second u y p q hu hp hq, hc, dot_unit_left, hyx] at h
    exact h.symm
  refine ⟨c, hcp, hcq, ?_⟩
  rw [Finset.sum_filter]
  calc
    _ = ∑ i, c i • twoFrame u y p q (unit i) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hip : i = p
      · subst i; simp [hcp]
      by_cases hiq : i = q
      · subst i; simp [hcq]
      simp [hip, hiq]
    _ = _ := (frame_decomposition u y c p q).trans hc

end
end ExactFourierCircuits.BinaryFrames

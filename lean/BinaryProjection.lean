import BinaryTensor
import FrameSpectrum
import BinaryResiduals

set_option autoImplicit false

namespace ExactFourierCircuits.BinaryProjection
open scoped BigOperators
open BinaryFrames BinaryTensor FrameSpectrum Module
noncomputable section

variable {ι κ α ν : Type*} [Fintype ι]

def frameSpan (z : κ → Vec ι) : Submodule F2 (Vec ι) := Submodule.span F2 (Set.range z)

def Orthonormal [DecidableEq κ] (z : κ → Vec ι) : Prop :=
  ∀ i j, dot (z i) (z j) = if i = j then 1 else 0

theorem dot_sub_right (x y z : Vec ι) : dot x (y - z) = dot x y - dot x z := by
  simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

section Projection
variable [Fintype κ] [DecidableEq κ]

omit [Fintype κ] in
theorem frame_unit (z : κ → Vec ι) (hz : Orthonormal z) (i : κ) : dot (z i) (z i) = 1 := by
  simpa using hz i i

omit [Fintype κ] in
theorem frame_orth (z : κ → Vec ι) (hz : Orthonormal z) (i j : κ) (hij : i ≠ j) :
    dot (z i) (z j) = 0 := by
  simpa [hij] using hz i j

omit [DecidableEq κ] in
theorem frameProjection_add (z : κ → Vec ι) (x y : Vec ι) :
    frameProjection z (x + y) = frameProjection z x + frameProjection z y := by
  simp only [frameProjection, dot_add_right, add_smul, Finset.sum_add_distrib]

omit [DecidableEq κ] in
theorem frameProjection_smul (z : κ → Vec ι) (c : F2) (x : Vec ι) :
    frameProjection z (c • x) = c • frameProjection z x := by
  simp only [frameProjection, dot_smul_right, mul_smul, Finset.smul_sum]

def projectionMap (z : κ → Vec ι) : Vec ι →ₗ[F2] Vec ι where
  toFun := frameProjection z
  map_add' := frameProjection_add z
  map_smul' c x := by simpa only [RingHom.id_apply] using frameProjection_smul z c x

def frameExponent (z : κ → Vec ι) (x : Vec ι) : ZMod 4 := weightModFour (frameProjection z x)

omit [DecidableEq κ] in
theorem frameProjection_mem_span (z : κ → Vec ι) (x : Vec ι) :
    frameProjection z x ∈ frameSpan z := by
  unfold frameProjection
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨i, rfl⟩

theorem frameProjection_generator (z : κ → Vec ι) (hz : Orthonormal z) (i : κ) :
    frameProjection z (z i) = z i := by
  rw [frameProjection]
  change ∀ i j, dot (z i) (z j) = if i = j then 1 else 0 at hz
  simp only [hz]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [hji]
  · simp

/-- Orthogonal projection fixes its entire actual span, not only its frame vectors. -/
theorem frameProjection_fixed_of_mem_span (z : κ → Vec ι) (hz : Orthonormal z)
    (x : Vec ι) (hx : x ∈ frameSpan z) : frameProjection z x = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact frameProjection_generator z hz i
  | zero => simp [frameProjection, dot]
  | add x y hx hy ix iy => rw [frameProjection_add, ix, iy]
  | smul c x hx ix => rw [frameProjection_smul, ix]

/-- The projection preserves all dot coefficients against its span. -/
theorem dot_projection_of_mem_span (z : κ → Vec ι) (hz : Orthonormal z)
    (x y : Vec ι) (hy : y ∈ frameSpan z) :
    dot y (frameProjection z x) = dot y x := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact frameProjection_dot z x (frame_orth z hz) (frame_unit z hz) i
  | zero => simp [dot]
  | add y t hy ht iy it => rw [dot_add_left, dot_add_left, iy, it]
  | smul c y hy iy => rw [dot_smul_left, dot_smul_left, iy]

/-- Membership in the span and matching frame coefficients characterize the projection. -/
theorem frameProjection_unique (z : κ → Vec ι) (hz : Orthonormal z)
    (x y : Vec ι) (hy : y ∈ frameSpan z)
    (hcoeff : ∀ i, dot (z i) y = dot (z i) x) : frameProjection z x = y := by
  have h : frameProjection z y = frameProjection z x := by
    unfold frameProjection
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcoeff i]
  exact h.symm.trans (frameProjection_fixed_of_mem_span z hz y hy)

theorem frameSpan_nondegenerate (z : κ → Vec ι) (hz : Orthonormal z) :
    BinaryResiduals.Nondegenerate (frameSpan z) := by
  intro x hx hzero
  have hfixed := frameProjection_fixed_of_mem_span z hz x hx
  have hprojection : frameProjection z x = 0 := by
    unfold frameProjection
    apply Finset.sum_eq_zero
    intro i hi
    rw [hzero (z i) (Submodule.subset_span ⟨i, rfl⟩), zero_smul]
  exact hfixed.symm.trans hprojection

theorem frameSpan_disjoint_residual (z : κ → Vec ι) (hz : Orthonormal z)
    (S : Submodule F2 (Vec ι)) :
    Disjoint (frameSpan z) (BinaryResiduals.residual (frameSpan z) S) := by
  rw [Submodule.disjoint_def]
  intro x hx hr
  exact frameSpan_nondegenerate z hz x hx hr.2

theorem frameProjection_remainder_mem_orth (z : κ → Vec ι) (hz : Orthonormal z) (x : Vec ι) :
    x - frameProjection z x ∈ BinaryResiduals.orth (frameSpan z) := by
  intro a ha
  rw [dot_sub_right, dot_projection_of_mem_span z hz x a ha, sub_self]

/-- A nested label splits into the smaller span and its actual orthogonal residual. -/
theorem frameSpan_decomposes_residual (z : κ → Vec ι) (hz : Orthonormal z)
    (S : Submodule F2 (Vec ι)) (hAS : frameSpan z ≤ S) :
    BinaryResiduals.Decomposes (frameSpan z) (BinaryResiduals.residual (frameSpan z) S) S := by
  refine ⟨?_, ?_⟩
  · apply le_antisymm
    · exact sup_le hAS inf_le_left
    · intro x hx
      let p := frameProjection z x
      have hp : p ∈ frameSpan z := frameProjection_mem_span z x
      have hr : x - p ∈ BinaryResiduals.residual (frameSpan z) S := by
        constructor
        · exact Submodule.sub_mem S hx (hAS hp)
        · intro a ha
          rw [dot_sub_right, dot_projection_of_mem_span z hz x a ha, sub_self]
      apply Submodule.mem_sup.mpr
      refine ⟨p, hp, x - p, hr, ?_⟩
      abel
  · intro a ha r hr
    exact hr.2 a ha

end Projection

section SameSpan
variable [Fintype κ] [DecidableEq κ] [Fintype α] [DecidableEq α]

/-- Basis independence follows from equality of actual spans. -/
theorem frameProjection_eq_of_span_eq (z : κ → Vec ι) (w : α → Vec ι)
    (hz : Orthonormal z) (hw : Orthonormal w)
    (hspan : frameSpan z = frameSpan w) (x : Vec ι) :
    frameProjection z x = frameProjection w x := by
  apply frameProjection_unique z hz x (frameProjection w x)
  · rw [hspan]
    exact frameProjection_mem_span w x
  · intro i
    apply dot_projection_of_mem_span w hw x (z i)
    rw [← hspan]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem projectionMap_eq_of_span_eq (z : κ → Vec ι) (w : α → Vec ι)
    (hz : Orthonormal z) (hw : Orthonormal w)
    (hspan : frameSpan z = frameSpan w) : projectionMap z = projectionMap w := by
  apply LinearMap.ext
  exact frameProjection_eq_of_span_eq z w hz hw hspan

variable [DecidableEq ι]

theorem signedWords_eq_of_span_eq (z : κ → Vec ι) (w : α → Vec ι)
    (decreasing : Bool) (hz : Orthonormal z) (hw : Orthonormal w)
    (hspan : frameSpan z = frameSpan w) :
    signedWord z decreasing Finset.univ.toList = signedWord w decreasing Finset.univ.toList := by
  apply signedWords_same_projection z w decreasing
    (frame_unit z hz) (frame_orth z hz) (frame_unit w hw) (frame_orth w hw)
  exact frameProjection_eq_of_span_eq z w hz hw hspan

theorem frameMap_eq_of_span_eq (z : κ → Vec ι) (w : α → Vec ι)
    (hz : Orthonormal z) (hw : Orthonormal w)
    (hspan : frameSpan z = frameSpan w) :
    frameMap (frameExponent z) = frameMap (frameExponent w) := by
  congr 1
  funext x
  rw [frameExponent, frameExponent, frameProjection_eq_of_span_eq z w hz hw hspan x]

end SameSpan

section DirectSum
variable [Fintype κ] [DecidableEq κ] [Fintype α] [DecidableEq α]
  [Fintype ν] [DecidableEq ν]

omit [DecidableEq κ] [DecidableEq α] in
theorem frameProjection_sumFamily (a : κ → Vec ι) (e : α → Vec ι) (x : Vec ι) :
    frameProjection (Sum.elim a e) x = frameProjection a x + frameProjection e x := by
  simp only [frameProjection, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

/-- Projection addition is derived from the actual orthogonal sum of label spaces. -/
theorem frameProjection_direct_sum (a : κ → Vec ι) (e : α → Vec ι) (v : ν → Vec ι)
    (ha : Orthonormal a) (he : Orthonormal e) (hv : Orthonormal v)
    (hD : BinaryResiduals.Decomposes (frameSpan a) (frameSpan e) (frameSpan v)) (x : Vec ι) :
    frameProjection v x = frameProjection a x + frameProjection e x := by
  have hcross : ∀ i j, dot (a i) (e j) = 0 := by
    intro i j
    exact hD.2 _ (Submodule.subset_span ⟨i, rfl⟩) _ (Submodule.subset_span ⟨j, rfl⟩)
  have hsum : Orthonormal (Sum.elim a e) := BinaryResiduals.sumFamily_orthonormal a e ha he hcross
  have hspan : frameSpan (Sum.elim a e) = frameSpan v := by
    calc
      _ = frameSpan a ⊔ frameSpan e := BinaryResiduals.sumFamily_span a e
      _ = _ := hD.1
  calc
    _ = frameProjection (Sum.elim a e) x :=
      (frameProjection_eq_of_span_eq (Sum.elim a e) v hsum hv hspan x).symm
    _ = _ := frameProjection_sumFamily a e x

theorem frameExponent_direct_sum (a : κ → Vec ι) (e : α → Vec ι) (v : ν → Vec ι)
    (ha : Orthonormal a) (he : Orthonormal e) (hv : Orthonormal v)
    (hD : BinaryResiduals.Decomposes (frameSpan a) (frameSpan e) (frameSpan v)) (x : Vec ι) :
    frameExponent v x = frameExponent a x + frameExponent e x := by
  unfold frameExponent
  rw [frameProjection_direct_sum a e v ha he hv hD x]
  apply weightModFour_add_of_dot_zero
  exact hD.2 _ (frameProjection_mem_span a x) _ (frameProjection_mem_span e x)

theorem residual_exponent_increasing (a : κ → Vec ι) (e : α → Vec ι) (v : ν → Vec ι)
    (ha : Orthonormal a) (he : Orthonormal e) (hv : Orthonormal v)
    (hD : BinaryResiduals.Decomposes (frameSpan a) (frameSpan e) (frameSpan v)) (x : Vec ι) :
    frameExponent v x - frameExponent a x = frameExponent e x := by
  rw [frameExponent_direct_sum a e v ha he hv hD x]
  ring

theorem residual_exponent_decreasing (a : κ → Vec ι) (e : α → Vec ι) (v : ν → Vec ι)
    (ha : Orthonormal a) (he : Orthonormal e) (hv : Orthonormal v)
    (hD : BinaryResiduals.Decomposes (frameSpan a) (frameSpan e) (frameSpan v)) (x : Vec ι) :
    frameExponent a x - frameExponent v x = -frameExponent e x := by
  rw [frameExponent_direct_sum a e v ha he hv hD x]
  ring

variable [DecidableEq ι]

theorem frame_ratio_increasing (a : κ → Vec ι) (e : α → Vec ι) (v : ν → Vec ι)
    (ha : Orthonormal a) (he : Orthonormal e) (hv : Orthonormal v)
    (hD : BinaryResiduals.Decomposes (frameSpan a) (frameSpan e) (frameSpan v)) :
    (frameMap (frameExponent v)).comp (frameMap (fun x => -frameExponent a x)) =
      signedWord e false Finset.univ.toList := by
  apply frame_ratio_signedWord (frameExponent a) (frameExponent v) e false
    (frame_unit e he) (frame_orth e he)
  intro x
  simpa only [edgeSign, Bool.false_eq_true, ↓reduceIte, one_mul, frameExponent] using
    residual_exponent_increasing a e v ha he hv hD x

theorem frame_ratio_decreasing (a : κ → Vec ι) (e : α → Vec ι) (v : ν → Vec ι)
    (ha : Orthonormal a) (he : Orthonormal e) (hv : Orthonormal v)
    (hD : BinaryResiduals.Decomposes (frameSpan a) (frameSpan e) (frameSpan v)) :
    (frameMap (frameExponent a)).comp (frameMap (fun x => -frameExponent v x)) =
      signedWord e true Finset.univ.toList := by
  apply frame_ratio_signedWord (frameExponent v) (frameExponent a) e true
    (frame_unit e he) (frame_orth e he)
  intro x
  simpa only [edgeSign, ↓reduceIte, neg_one_mul, frameExponent] using
    residual_exponent_decreasing a e v ha he hv hD x

/-- Actual nesting and equality with the geometric residual discharge the decomposition. -/
theorem nested_frame_ratio_increasing (a : κ → Vec ι) (e : α → Vec ι) (v : ν → Vec ι)
    (ha : Orthonormal a) (he : Orthonormal e) (hv : Orthonormal v)
    (hAV : frameSpan a ≤ frameSpan v)
    (hE : frameSpan e = BinaryResiduals.residual (frameSpan a) (frameSpan v)) :
    (frameMap (frameExponent v)).comp (frameMap (fun x => -frameExponent a x)) =
      signedWord e false Finset.univ.toList := by
  have hD := frameSpan_decomposes_residual a ha (frameSpan v) hAV
  rw [← hE] at hD
  exact frame_ratio_increasing a e v ha he hv hD

theorem nested_frame_ratio_decreasing (a : κ → Vec ι) (e : α → Vec ι) (v : ν → Vec ι)
    (ha : Orthonormal a) (he : Orthonormal e) (hv : Orthonormal v)
    (hAV : frameSpan a ≤ frameSpan v)
    (hE : frameSpan e = BinaryResiduals.residual (frameSpan a) (frameSpan v)) :
    (frameMap (frameExponent a)).comp (frameMap (fun x => -frameExponent v x)) =
      signedWord e true Finset.univ.toList := by
  have hD := frameSpan_decomposes_residual a ha (frameSpan v) hAV
  rw [← hE] at hD
  exact frame_ratio_decreasing a e v ha he hv hD

end DirectSum

section Bases
variable [Fintype κ] [DecidableEq κ] [Fintype α] [DecidableEq α]
  [Fintype ν] [DecidableEq ν] [DecidableEq ι]

omit [DecidableEq ι] in
theorem basis_projection_same_space (A : Submodule F2 (Vec ι))
    (a : Basis κ F2 A) (b : Basis α F2 A)
    (ha : Orthonormal (fun i => (a i : Vec ι)))
    (hb : Orthonormal (fun i => (b i : Vec ι))) (x : Vec ι) :
    frameProjection (fun i => (a i : Vec ι)) x = frameProjection (fun i => (b i : Vec ι)) x := by
  apply frameProjection_eq_of_span_eq _ _ ha hb
  exact (BinaryResiduals.basis_span_coe A a).trans (BinaryResiduals.basis_span_coe A b).symm

/-- This basis interface uses the actual smaller, residual and larger submodules. -/
theorem nested_basis_ratio_increasing (A S : Submodule F2 (Vec ι)) (hAS : A ≤ S)
    (a : Basis κ F2 A) (e : Basis α F2 (BinaryResiduals.residual A S)) (v : Basis ν F2 S)
    (ha : Orthonormal (fun i => (a i : Vec ι)))
    (he : Orthonormal (fun i => (e i : Vec ι)))
    (hv : Orthonormal (fun i => (v i : Vec ι))) :
    (frameMap (frameExponent (fun i => (v i : Vec ι)))).comp
      (frameMap (fun x => -frameExponent (fun i => (a i : Vec ι)) x)) =
      signedWord (fun i => (e i : Vec ι)) false Finset.univ.toList := by
  apply nested_frame_ratio_increasing _ _ _ ha he hv
  · simpa only [frameSpan, BinaryResiduals.basis_span_coe] using hAS
  · simp only [frameSpan, BinaryResiduals.basis_span_coe]

theorem nested_basis_ratio_decreasing (A S : Submodule F2 (Vec ι)) (hAS : A ≤ S)
    (a : Basis κ F2 A) (e : Basis α F2 (BinaryResiduals.residual A S)) (v : Basis ν F2 S)
    (ha : Orthonormal (fun i => (a i : Vec ι)))
    (he : Orthonormal (fun i => (e i : Vec ι)))
    (hv : Orthonormal (fun i => (v i : Vec ι))) :
    (frameMap (frameExponent (fun i => (a i : Vec ι)))).comp
      (frameMap (fun x => -frameExponent (fun i => (v i : Vec ι)) x)) =
      signedWord (fun i => (e i : Vec ι)) true Finset.univ.toList := by
  apply nested_frame_ratio_decreasing _ _ _ ha he hv
  · simpa only [frameSpan, BinaryResiduals.basis_span_coe] using hAS
  · simp only [frameSpan, BinaryResiduals.basis_span_coe]

end Bases

end
end ExactFourierCircuits.BinaryProjection

import BinaryFrames
set_option autoImplicit false

/- Completes the conditional coordinate-frame construction using the characteristic
   vector argument and the paper's support bounds (network.tex, orthonormal residuals).
   Sparse encoding, ordered pivot search, tensor residuals and the full network remain separate. -/
namespace ExactFourierCircuits.BinaryComplement
open ExactFourierCircuits.BinaryFrames
open Module
open scoped BigOperators
noncomputable section

lemma f2_cases (x : F2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma f2_square (x : F2) : x * x = x := by
  rcases f2_cases x with rfl | rfl <;> norm_num

def characteristic {ι : Type*} : Vec ι := fun _ => 1

variable {ι : Type*} [Fintype ι]

lemma dot_characteristic (v : Vec ι) : dot v characteristic = dot v v := by
  unfold dot characteristic
  apply Finset.sum_congr rfl
  intro i hi
  simp [f2_square]

theorem transvection_fixes_characteristic (v : Vec ι) (hv : dot v v = 0) :
    transvection v characteristic = characteristic := by
  rw [transvection_apply, dot_characteristic, hv, zero_smul, add_zero]

omit [Fintype ι] in
theorem exists_zero_iff_not_characteristic (u : Vec ι) :
    (∃ p, u p = 0) ↔ u ≠ characteristic := by
  constructor
  · rintro ⟨p, hp⟩ h
    have h1 := congrFun h p
    simp [characteristic, hp] at h1
  · intro h
    by_contra hn
    apply h
    funext i
    rcases f2_cases (u i) with h0 | h1
    · exact (hn ⟨i, h0⟩).elim
    · exact h1

variable [DecidableEq ι]

/-- The image of every remaining coordinate unit is perpendicular to u. -/
theorem one_complement_orthogonal (u : Vec ι) (p : ι)
    (hu : dot u u = 1) (hp : u p = 0) (j : ι) (hjp : j ≠ p) :
    dot u (transvection (unit p + u) (unit j)) = 0 := by
  calc
    _ = dot (transvection (unit p + u) (unit p))
        (transvection (unit p + u) (unit j)) := by rw [pivot_transvection_unit u p hp]
    _ = dot (unit p) (unit j) := transvection_preserves_dot _
      (pivot_direction_isotropic u p hu hp) _ _
    _ = 0 := by simp [unit, hjp]

theorem one_complement_spans (u : Vec ι) (p : ι)
    (hu : dot u u = 1) (hp : u p = 0) (x : Vec ι) (hux : dot u x = 0) :
    ∃ c : Vec ι, c p = 0 ∧
      (∑ i ∈ Finset.univ.filter (fun i => i ≠ p),
        c i • transvection (unit p + u) (unit i)) = x := by
  let E := transvectionEquiv (unit p + u) (pivot_direction_isotropic u p hu hp)
  let c := E.symm x
  have hc : transvection (unit p + u) c = x := E.apply_symm_apply x
  have hcp : c p = 0 := by
    have h := transvection_preserves_dot (unit p + u)
      (pivot_direction_isotropic u p hu hp) (unit p) c
    rw [pivot_transvection_unit u p hp, hc, dot_unit_left, hux] at h
    exact h.symm
  refine ⟨c, hcp, ?_⟩
  rw [Finset.sum_filter]
  calc
    _ = ∑ i, c i • transvection (unit p + u) (unit i) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hip : i = p
      · subst i; simp [hcp]
      · simp [hip]
    _ = transvection (unit p + u) (∑ i, c i • unit i) := by
      simp only [map_sum, map_smul]
    _ = _ := by rw [unit_decomposition c, hc]

abbrev OneIndex (p : ι) := {i : ι // i ≠ p}
abbrev TwoIndex (p q : ι) := {i : ι // i ≠ p ∧ i ≠ q}

theorem one_index_card (p : ι) : Fintype.card (OneIndex p) = Fintype.card ι - 1 := by
  change Fintype.card {i : ι // ¬ i = p} = Fintype.card ι - 1
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

theorem two_index_card (p q : ι) (hqp : q ≠ p) :
    Fintype.card (TwoIndex p q) = Fintype.card ι - 2 := by
  rw [Fintype.card_subtype]
  have he : Finset.univ.filter (fun i : ι => i ≠ p ∧ i ≠ q) =
      (Finset.univ.erase p).erase q := by
    ext i
    simp [and_comm]
  rw [he, Finset.card_erase_of_mem (by simp [hqp]),
    Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ]
  omega

omit [Fintype ι] in
/-- If the second search fails, its transformed vector is chi+e_p. -/
lemma failed_second_pivot_shape (w : Vec ι) (p : ι) (hp : w p = 0)
    (hn : ¬ ∃ q, q ≠ p ∧ w q = 0) : w = characteristic + unit p := by
  funext i
  by_cases hip : i = p
  · subst i
    simp [characteristic, unit, hp, CharTwo.add_self_eq_zero]
  · rcases f2_cases (w i) with h0 | h1
    · exact (hn ⟨i, hip, h0⟩).elim
    · simp [characteristic, unit, hip, h1]

theorem exists_second_pivot (u y : Vec ι) (p : ι)
    (hu : dot u u = 1) (huy : dot u y = 0) (hp : u p = 0)
    (hsum : u + y ≠ characteristic) : ∃ q, q ≠ p ∧ firstImage u y p q = 0 := by
  by_contra hn
  have hw := failed_second_pivot_shape (firstImage u y p) p
    (firstImage_pivot_zero u y p huy hp) hn
  have hv := pivot_direction_isotropic u p hu hp
  have hy : y = characteristic + u := by
    calc
      y = transvection (unit p + u) (firstImage u y p) :=
        (transvection_involutive _ hv y).symm
      _ = transvection (unit p + u) (characteristic + unit p) := by rw [hw]
      _ = _ := by rw [transvection_add, transvection_fixes_characteristic _ hv,
        pivot_transvection_unit u p hp]
  apply hsum
  rw [hy]
  ext i
  change u i + (1 + u i) = 1
  calc
    _ = 1 + (u i + u i) := by ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]

theorem exists_valid_pivots (u y : Vec ι) (hu : dot u u = 1)
    (huy : dot u y = 0) (huchi : u ≠ characteristic) (hsum : u + y ≠ characteristic) :
    ∃ p q, u p = 0 ∧ q ≠ p ∧ firstImage u y p q = 0 := by
  obtain ⟨p, hp⟩ := (exists_zero_iff_not_characteristic u).mpr huchi
  obtain ⟨q, hqp, hq⟩ := exists_second_pivot u y p hu huy hp hsum
  exact ⟨p, q, hp, hqp, hq⟩

/-- Orthogonal complement as a genuine submodule of the finite binary vector space. -/
def perp (u : Vec ι) : Submodule F2 (Vec ι) where
  carrier := {x | dot u x = 0}
  zero_mem' := by simp [dot]
  add_mem' := by
    intro x y hx hy
    change dot u x = 0 at hx
    change dot u y = 0 at hy
    change dot u (x + y) = 0
    rw [dot_add_right, hx, hy, add_zero]
  smul_mem' := by
    intro c x hx
    change dot u x = 0 at hx
    change dot u (c • x) = 0
    rw [dot_smul_right, hx, mul_zero]

omit [DecidableEq ι] in
@[simp] lemma mem_perp (u x : Vec ι) : x ∈ perp u ↔ dot u x = 0 := Iff.rfl

abbrev pairPerp (u y : Vec ι) := perp u ⊓ perp y

def oneFamily (u : Vec ι) (p : ι) : OneIndex p → Vec ι :=
  fun j => transvection (unit p + u) (unit j.val)

def twoFamily (u y : Vec ι) (p q : ι) : TwoIndex p q → Vec ι :=
  fun j => twoFrame u y p q (unit j.val)

def oneAmbientBasis (u : Vec ι) (p : ι) (hu : dot u u = 1) (hp : u p = 0) :
    Basis ι F2 (Vec ι) :=
  (Pi.basisFun F2 ι).map (transvectionEquiv _ (pivot_direction_isotropic u p hu hp))

lemma oneAmbientBasis_apply (u : Vec ι) (p : ι)
    (hu : dot u u = 1) (hp : u p = 0) (j : ι) :
    oneAmbientBasis u p hu hp j = transvection (unit p + u) (unit j) := by
  simp only [oneAmbientBasis, Basis.map_apply, transvectionEquiv_apply, Pi.basisFun_apply]
  congr 1
  funext i
  simp [Pi.single_apply, unit, eq_comm]

def twoAmbientBasis (u y : Vec ι) (p q : ι)
    (hu : dot u u = 1) (hy : dot y y = 1) (hp : u p = 0)
    (hq : firstImage u y p q = 0) : Basis ι F2 (Vec ι) :=
  (Pi.basisFun F2 ι).map (twoFrameEquiv u y p q hu hy hp hq)

lemma twoAmbientBasis_apply (u y : Vec ι) (p q : ι)
    (hu : dot u u = 1) (hy : dot y y = 1) (hp : u p = 0)
    (hq : firstImage u y p q = 0) (j : ι) :
    twoAmbientBasis u y p q hu hy hp hq j = twoFrame u y p q (unit j) := by
  simp only [twoAmbientBasis, Basis.map_apply, twoFrameEquiv_apply, Pi.basisFun_apply]
  congr 1
  funext i
  simp [Pi.single_apply, unit, eq_comm]

lemma oneFamily_linearIndependent (u : Vec ι) (p : ι)
    (hu : dot u u = 1) (hp : u p = 0) : LinearIndependent F2 (oneFamily u p) := by
  have h := (oneAmbientBasis u p hu hp).linearIndependent.comp
    (fun j : OneIndex p => j.val) Subtype.val_injective
  change LinearIndependent F2
    (fun j : OneIndex p => transvection (unit p + u) (unit j.val))
  simpa only [Function.comp_def, oneAmbientBasis_apply, oneFamily] using h

lemma twoFamily_linearIndependent (u y : Vec ι) (p q : ι)
    (hu : dot u u = 1) (hy : dot y y = 1) (hp : u p = 0)
    (hq : firstImage u y p q = 0) : LinearIndependent F2 (twoFamily u y p q) := by
  have h := (twoAmbientBasis u y p q hu hy hp hq).linearIndependent.comp
    (fun j : TwoIndex p q => j.val) Subtype.val_injective
  change LinearIndependent F2 (fun j : TwoIndex p q => twoFrame u y p q (unit j.val))
  simpa only [Function.comp_def, twoAmbientBasis_apply, twoFamily] using h

lemma oneFamily_span (u : Vec ι) (p : ι)
    (hu : dot u u = 1) (hp : u p = 0) :
    Submodule.span F2 (Set.range (oneFamily u p)) = perp u := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    exact one_complement_orthogonal u p hu hp j.val j.property
  · intro x hx
    obtain ⟨c, hc, he⟩ := one_complement_spans u p hu hp x hx
    rw [← he]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨⟨i, (Finset.mem_filter.mp hi).2⟩, rfl⟩

lemma twoFamily_span (u y : Vec ι) (p q : ι)
    (hu : dot u u = 1) (hy : dot y y = 1) (huy : dot u y = 0)
    (hp : u p = 0) (hqp : q ≠ p) (hq : firstImage u y p q = 0) :
    Submodule.span F2 (Set.range (twoFamily u y p q)) = pairPerp u y := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    exact twoFrame_complement_orthogonal u y p q hu hy huy hp hqp hq
      j.val j.property.1 j.property.2
  · intro x hx
    obtain ⟨c, hcp, hcq, he⟩ := twoFrame_complement_spans u y p q hu hy huy hp hqp hq
      x hx.1 hx.2
    rw [← he]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨⟨i, (Finset.mem_filter.mp hi).2⟩, rfl⟩

/-- Actual basis, with exactly n-1 coordinate indices. -/
def oneComplementBasis (u : Vec ι) (p : ι) (hu : dot u u = 1) (hp : u p = 0) :
    Basis (OneIndex p) F2 (perp u) :=
  (Basis.span (oneFamily_linearIndependent u p hu hp)).map
    (LinearEquiv.ofEq _ _ (oneFamily_span u p hu hp))

/-- Actual basis, with exactly n-2 coordinate indices and Python's composition order. -/
def twoComplementBasis (u y : Vec ι) (p q : ι)
    (hu : dot u u = 1) (hy : dot y y = 1) (huy : dot u y = 0)
    (hp : u p = 0) (hqp : q ≠ p) (hq : firstImage u y p q = 0) :
    Basis (TwoIndex p q) F2 (pairPerp u y) :=
  (Basis.span (twoFamily_linearIndependent u y p q hu hy hp hq)).map
    (LinearEquiv.ofEq _ _ (twoFamily_span u y p q hu hy huy hp hqp hq))

@[simp] theorem oneComplementBasis_apply (u : Vec ι) (p : ι)
    (hu : dot u u = 1) (hp : u p = 0) (j : OneIndex p) :
    (oneComplementBasis u p hu hp j : Vec ι) = transvection (unit p + u) (unit j.val) := by
  simp [oneComplementBasis, oneFamily]

@[simp] theorem twoComplementBasis_apply (u y : Vec ι) (p q : ι)
    (hu : dot u u = 1) (hy : dot y y = 1) (huy : dot u y = 0)
    (hp : u p = 0) (hqp : q ≠ p) (hq : firstImage u y p q = 0) (j : TwoIndex p q) :
    (twoComplementBasis u y p q hu hy huy hp hqp hq j : Vec ι) =
      twoFrame u y p q (unit j.val) := by
  simp [twoComplementBasis, twoFamily]

theorem oneComplementBasis_orthonormal (u : Vec ι) (p : ι)
    (hu : dot u u = 1) (hp : u p = 0) (i j : OneIndex p) :
    dot (oneComplementBasis u p hu hp i : Vec ι)
      (oneComplementBasis u p hu hp j : Vec ι) = if i = j then 1 else 0 := by
  rw [oneComplementBasis_apply, oneComplementBasis_apply,
    transvection_preserves_dot _ (pivot_direction_isotropic u p hu hp), dot_units]
  simp only [Subtype.val_inj]

theorem twoComplementBasis_orthonormal (u y : Vec ι) (p q : ι)
    (hu : dot u u = 1) (hy : dot y y = 1) (huy : dot u y = 0)
    (hp : u p = 0) (hqp : q ≠ p) (hq : firstImage u y p q = 0)
    (i j : TwoIndex p q) :
    dot (twoComplementBasis u y p q hu hy huy hp hqp hq i : Vec ι)
      (twoComplementBasis u y p q hu hy huy hp hqp hq j : Vec ι) =
      if i = j then 1 else 0 := by
  rw [twoComplementBasis_apply, twoComplementBasis_apply,
    twoFrame_orthonormal u y p q hu hy hp hq]
  simp only [Subtype.val_inj]

def indicator (s : Finset ι) : Vec ι := fun i => if i ∈ s then 1 else 0

lemma dot_indicators (s t : Finset ι) : dot (indicator s) (indicator t) = ((s ∩ t).card : F2) := by
  calc
    _ = ∑ i, if i ∈ s ∩ t then (1 : F2) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [indicator, hs, ht]
    _ = _ := by
      rw [← Finset.sum_filter]
      have hf : Finset.univ.filter (fun i : ι => i ∈ s ∩ t) = s ∩ t := by
        ext i
        simp
      rw [hf]
      simp

theorem triple_indicator_norm (s : Finset ι) (hs : s.card = 3) :
    dot (indicator s) (indicator s) = 1 := by
  rw [dot_indicators, Finset.inter_self, hs]
  calc
    (3 : F2) = (1 + 1 : F2) + 1 := by ring
    _ = 1 := by rw [CharTwo.add_self_eq_zero, zero_add]

omit [DecidableEq ι] in
lemma exists_outside (s : Finset ι) (hs : s.card < Fintype.card ι) : ∃ i, i ∉ s := by
  obtain ⟨i, hi, his⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show s.card < Finset.univ.card by simpa using hs)
  exact ⟨i, his⟩

theorem triple_indicator_not_characteristic (s : Finset ι)
    (hs : s.card = 3) (hn : 7 ≤ Fintype.card ι) : indicator s ≠ characteristic := by
  obtain ⟨i, hi⟩ := exists_outside s (by omega)
  intro h
  have he := congrFun h i
  simp [indicator, characteristic, hi] at he

theorem triple_indicator_valid_pivot (s : Finset ι)
    (hs : s.card = 3) (hn : 7 ≤ Fintype.card ι) : ∃ p, indicator s p = 0 := by
  exact (exists_zero_iff_not_characteristic _).mpr
    (triple_indicator_not_characteristic s hs hn)

/-- The one-triple complement has an orthonormal basis indexed by the other coordinates. -/
theorem triple_basis_exists (s : Finset ι) (hs : s.card = 3)
    (hn : 7 ≤ Fintype.card ι) :
    ∃ p, ∃ b : Basis (OneIndex p) F2 (perp (indicator s)),
      ∀ j, (b j : Vec ι) = transvection (unit p + indicator s) (unit j.val) := by
  obtain ⟨p, hp⟩ := triple_indicator_valid_pivot s hs hn
  refine ⟨p, oneComplementBasis _ p (triple_indicator_norm s hs) hp, ?_⟩
  intro j
  exact oneComplementBasis_apply _ _ _ _ j

theorem triple_pair_sum_not_characteristic (s t : Finset ι)
    (hs : s.card = 3) (ht : t.card = 3) (hn : 7 ≤ Fintype.card ι) :
    indicator s + indicator t ≠ characteristic := by
  have hcard := Finset.card_union_le s t
  obtain ⟨i, hi⟩ := exists_outside (s ∪ t) (by omega)
  have his : i ∉ s := fun h => hi (Finset.mem_union_left t h)
  have hit : i ∉ t := fun h => hi (Finset.mem_union_right s h)
  intro h
  have he := congrFun h i
  simp [indicator, characteristic, his, hit] at he

theorem even_intersection_orthogonal (s t : Finset ι) (he : Even (s ∩ t).card) :
    dot (indicator s) (indicator t) = 0 := by
  rw [dot_indicators]
  simpa [he] using (CharTwo.natCast_eq_ite (R := F2) (s ∩ t).card)

/-- Both searches have valid pivots for every orthogonal triple pair when n≥7. -/
theorem triple_pair_valid_pivots (s t : Finset ι)
    (hs : s.card = 3) (ht : t.card = 3) (he : Even (s ∩ t).card)
    (hn : 7 ≤ Fintype.card ι) :
    ∃ p q, indicator s p = 0 ∧ q ≠ p ∧ firstImage (indicator s) (indicator t) p q = 0 := by
  exact exists_valid_pivots _ _ (triple_indicator_norm s hs)
    (even_intersection_orthogonal s t he) (triple_indicator_not_characteristic s hs hn)
    (triple_pair_sum_not_characteristic s t hs ht hn)

/-- The paper's triple-pair complement is packaged as a basis with the actual frame images. -/
theorem triple_pair_basis_exists (s t : Finset ι)
    (hs : s.card = 3) (ht : t.card = 3) (he : Even (s ∩ t).card)
    (hn : 7 ≤ Fintype.card ι) :
    ∃ p q, ∃ b : Basis (TwoIndex p q) F2 (pairPerp (indicator s) (indicator t)),
      ∀ j, (b j : Vec ι) = twoFrame (indicator s) (indicator t) p q (unit j.val) := by
  obtain ⟨p, q, hp, hqp, hq⟩ := triple_pair_valid_pivots s t hs ht he hn
  refine ⟨p, q, twoComplementBasis _ _ p q
    (triple_indicator_norm s hs) (triple_indicator_norm t ht)
    (even_intersection_orthogonal s t he) hp hqp hq, ?_⟩
  intro j
  exact twoComplementBasis_apply _ _ _ _ _ _ _ _ _ _ j

end
end ExactFourierCircuits.BinaryComplement

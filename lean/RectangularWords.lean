import RoleWords

set_option autoImplicit false

namespace ExactFourierCircuits.RectangularWords
open OAI.ExactFourier RoleWords TypedKernelWords
open scoped BigOperators
noncomputable section

variable {a b r : ℕ}

def support (M : Matrix (Fin a) (Fin b) ℂ) : Finset (Fin a × Fin b) := by
  classical
  exact Finset.univ.filter (fun ij => M ij.1 ij.2 ≠ 0)

lemma mem_support (M : Matrix (Fin a) (Fin b) ℂ) (ij : Fin a × Fin b) :
    ij ∈ support M ↔ M ij.1 ij.2 ≠ 0 := by classical simp [support]

abbrev Entry (M : Matrix (Fin a) (Fin b) ℂ) := {ij : Fin a × Fin b // ij ∈ support M}

def entryMatrix (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (M : Matrix (Fin a) (Fin b) ℂ) (ij : Fin a × Fin b) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.single (dest ij.1) (source ij.2) (M ij.1 ij.2)

def entryWord (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : ∀ i j, dest i ≠ source j) (M : Matrix (Fin a) (Fin b) ℂ) (e : Entry M) :
    List (WordStep C r) :=
  roleShearWord (dest e.val.1) (source e.val.2) (hd _ _) (M e.val.1 e.val.2)
    ((mem_support M e.val).mp e.property)

lemma entryWord_matrix (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : ∀ i j, dest i ≠ source j) (M : Matrix (Fin a) (Fin b) ℂ) (e : Entry M) :
    wordMatrix (entryWord dest source hd M e) = 1 + entryMatrix dest source M e.val :=
  roleShearWord_matrix _ _ _ _ _

lemma entryWord_calls (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : ∀ i j, dest i ≠ source j) (M : Matrix (Fin a) (Fin b) ℂ) (e : Entry M) :
    wordCalls (entryWord dest source hd M e) = 3 := roleShearWord_calls _ _ _ _ _

/-- The products vanish because no source role is a destination role. -/
lemma entryMatrix_mul_zero (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : ∀ i j, dest i ≠ source j) (M : Matrix (Fin a) (Fin b) ℂ)
    (ij kl : Fin a × Fin b) :
    entryMatrix dest source M ij * entryMatrix dest source M kl = 0 :=
  Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm (hd kl.1 ij.2)) _

def listWord (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : ∀ i j, dest i ≠ source j) (M : Matrix (Fin a) (Fin b) ℂ) (L : List (Entry M)) :
    List (WordStep C r) := (L.map (entryWord dest source hd M)).flatten

lemma entrySum_mul_zero (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : ∀ i j, dest i ≠ source j) (M : Matrix (Fin a) (Fin b) ℂ)
    (L : List (Entry M)) (e : Entry M) :
    (L.map (fun x => entryMatrix dest source M x.val)).sum * entryMatrix dest source M e.val = 0 := by
  induction L with
  | nil => simp
  | cons k L ih =>
    simp only [List.map_cons, List.sum_cons, Matrix.add_mul, entryMatrix_mul_zero dest source hd M,
      ih, add_zero]

/-- This is an expansion of the literal chronological word, not a supplied matrix identity. -/
lemma listWord_matrix (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : ∀ i j, dest i ≠ source j) (M : Matrix (Fin a) (Fin b) ℂ) (L : List (Entry M)) :
    wordMatrix (listWord dest source hd M L) =
      1 + (L.map (fun x => entryMatrix dest source M x.val)).sum := by
  induction L with
  | nil => simp [listWord, wordMatrix]
  | cons e L ih =>
    change wordMatrix (entryWord dest source hd M e ++ listWord dest source hd M L) = _
    rw [wordMatrix_append, ih, entryWord_matrix]
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one,
      entrySum_mul_zero dest source hd M L e, add_zero]
    simp only [List.map_cons, List.sum_cons]
    abel

lemma listWord_calls (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : ∀ i j, dest i ≠ source j) (M : Matrix (Fin a) (Fin b) ℂ) (L : List (Entry M)) :
    wordCalls (listWord dest source hd M L) = 3 * L.length := by
  induction L with
  | nil => simp [listWord, wordCalls]
  | cons e L ih =>
    change wordCalls (entryWord dest source hd M e ++ listWord dest source hd M L) = _
    rw [wordCalls_append, entryWord_calls, ih]
    simp only [List.length_cons]
    omega

/-- Enumerate exactly the nonzero entries, then concatenate their actual three-call words. -/
def rectangularWord (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : ∀ i j, dest i ≠ source j) (M : Matrix (Fin a) (Fin b) ℂ) : List (WordStep C r) :=
  listWord dest source hd M (support M).attach.toList

def rectangularMatrix (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (M : Matrix (Fin a) (Fin b) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  1 + ∑ ij : Fin a × Fin b, entryMatrix dest source M ij

lemma support_sum_eq_univ (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (M : Matrix (Fin a) (Fin b) ℂ) :
    (∑ ij ∈ support M, entryMatrix dest source M ij) = ∑ ij, entryMatrix dest source M ij := by
  classical
  rw [support, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ij hij
  by_cases he : M ij.1 ij.2 ≠ 0
  · simp [he]
  · simp [not_ne_iff.mp he, entryMatrix]

lemma rectangularWord_matrix (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : ∀ i j, dest i ≠ source j) (M : Matrix (Fin a) (Fin b) ℂ) :
    wordMatrix (rectangularWord dest source hd M) = rectangularMatrix dest source M := by
  rw [rectangularWord, listWord_matrix, Finset.sum_map_toList, Finset.sum_attach,
    support_sum_eq_univ]
  rfl

lemma rectangularWord_calls (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : ∀ i j, dest i ≠ source j) (M : Matrix (Fin a) (Fin b) ℂ) :
    wordCalls (rectangularWord dest source hd M) = 3 * (support M).card := by
  rw [rectangularWord, listWord_calls]
  simp


/-- Every role is updated from the original source vector, because all cross products are zero. -/
lemma rectangularWord_apply (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : ∀ i j, dest i ≠ source j) (M : Matrix (Fin a) (Fin b) ℂ)
    (X : Fin r → ℂ) (k : Fin r) :
    (wordMatrix (rectangularWord dest source hd M)).mulVec X k =
      X k + ∑ ij : Fin a × Fin b,
        if k = dest ij.1 then M ij.1 ij.2 * X (source ij.2) else 0 := by
  rw [rectangularWord_matrix, rectangularMatrix, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec]
  simp [entryMatrix, Matrix.single_mulVec, Function.update_apply]

lemma rectangularWord_target (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : ∀ i j, dest i ≠ source j) (M : Matrix (Fin a) (Fin b) ℂ)
    (X : Fin r → ℂ) (i : Fin a) :
    (wordMatrix (rectangularWord dest source hd M)).mulVec X (dest i) =
      X (dest i) + M.mulVec (fun j => X (source j)) i := by
  rw [rectangularWord_apply, Fintype.sum_prod_type]
  simp [dest.injective.eq_iff, Matrix.mulVec, dotProduct]

lemma rectangularWord_untouched (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : ∀ i j, dest i ≠ source j) (M : Matrix (Fin a) (Fin b) ℂ)
    (X : Fin r → ℂ) (k : Fin r) (hk : k ∉ Set.range dest) :
    (wordMatrix (rectangularWord dest source hd M)).mulVec X k = X k := by
  rw [rectangularWord_apply]
  have hne (ij : Fin a × Fin b) : k ≠ dest ij.1 := by
    intro he
    exact hk ⟨ij.1, he.symm⟩
  simp [hne]

lemma rectangularWord_source (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : ∀ i j, dest i ≠ source j) (M : Matrix (Fin a) (Fin b) ℂ)
    (X : Fin r → ℂ) (j : Fin b) :
    (wordMatrix (rectangularWord dest source hd M)).mulVec X (source j) = X (source j) := by
  apply rectangularWord_untouched
  rintro ⟨i, he⟩
  exact hd i j he

/-- The literal role word is copied onto every address fiber. -/
def pointwiseRectangularWord (n : ℕ) (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : ∀ i j, dest i ≠ source j) (M : Matrix (Fin a) (Fin b) ℂ) :
    List (WordStep C (r * 2 ^ n)) := pointwiseWord n (rectangularWord dest source hd M)

lemma pointwiseRectangularWord_matrix (n : ℕ) (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : ∀ i j, dest i ≠ source j) (M : Matrix (Fin a) (Fin b) ℂ) :
    wordMatrix (pointwiseRectangularWord n dest source hd M) =
      pointwiseMatrix n (rectangularMatrix dest source M) := by
  rw [pointwiseRectangularWord, pointwiseWord_matrix, rectangularWord_matrix]

lemma pointwiseRectangularWord_calls (n : ℕ) (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : ∀ i j, dest i ≠ source j) (M : Matrix (Fin a) (Fin b) ℂ) :
    wordCalls (pointwiseRectangularWord n dest source hd M) = 3 * (support M).card * 2 ^ n := by
  rw [pointwiseRectangularWord, pointwiseWord_calls, rectangularWord_calls]
  ring

lemma pointwiseRectangularWord_target (n : ℕ) (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : ∀ i j, dest i ≠ source j) (M : Matrix (Fin a) (Fin b) ℂ)
    (X : Fin r → Fin (2 ^ n) → ℂ) (i : Fin a) (x : Fin (2 ^ n)) :
    (wordMatrix (pointwiseRectangularWord n dest source hd M)).mulVec (arrayValues n X)
      (roleAddresses r n (dest i, x)) = X (dest i) x + M.mulVec (fun j => X (source j) x) i := by
  rw [pointwiseRectangularWord, pointwiseWord_apply, rectangularWord_target]

lemma pointwiseRectangularWord_untouched (n : ℕ) (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : ∀ i j, dest i ≠ source j) (M : Matrix (Fin a) (Fin b) ℂ)
    (X : Fin r → Fin (2 ^ n) → ℂ) (k : Fin r) (hk : k ∉ Set.range dest) (x : Fin (2 ^ n)) :
    (wordMatrix (pointwiseRectangularWord n dest source hd M)).mulVec (arrayValues n X)
      (roleAddresses r n (k, x)) = X k x := by
  rw [pointwiseRectangularWord, pointwiseWord_apply, rectangularWord_untouched dest source hd M _ k hk]

lemma pointwiseRectangularWord_source (n : ℕ) (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : ∀ i j, dest i ≠ source j) (M : Matrix (Fin a) (Fin b) ℂ)
    (X : Fin r → Fin (2 ^ n) → ℂ) (j : Fin b) (x : Fin (2 ^ n)) :
    (wordMatrix (pointwiseRectangularWord n dest source hd M)).mulVec (arrayValues n X)
      (roleAddresses r n (source j, x)) = X (source j) x := by
  rw [pointwiseRectangularWord, pointwiseWord_apply, rectangularWord_source]

/-- Equality on arbitrary arrays, including every target and untouched role. -/
lemma pointwiseRectangularWord_array (n : ℕ) (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : ∀ i j, dest i ≠ source j) (M : Matrix (Fin a) (Fin b) ℂ)
    (X : Fin r → Fin (2 ^ n) → ℂ) :
    (wordMatrix (pointwiseRectangularWord n dest source hd M)).mulVec (arrayValues n X) =
      arrayValues n (fun k x => X k x + ∑ ij : Fin a × Fin b,
        if k = dest ij.1 then M ij.1 ij.2 * X (source ij.2) x else 0) := by
  rw [pointwiseRectangularWord, pointwiseWord_array]
  congr 1
  funext k x
  exact rectangularWord_apply dest source hd M (fun j => X j x) k

lemma disjoint_ranges (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : Disjoint (Set.range dest) (Set.range source)) : ∀ i j, dest i ≠ source j := by
  intro i j he
  exact Set.disjoint_left.mp hd ⟨i, rfl⟩ ⟨j, he.symm⟩

/-- No supplied full matrix identity is used: the enumerated word and its count are constructed. -/
theorem compile_rectangular_shear (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : Disjoint (Set.range dest) (Set.range source)) (M : Matrix (Fin a) (Fin b) ℂ) :
    ∃ W : List (WordStep C r), wordMatrix W = rectangularMatrix dest source M ∧
      wordCalls W = 3 * (support M).card ∧
      (∀ X i, (wordMatrix W).mulVec X (dest i) = X (dest i) + M.mulVec (fun j => X (source j)) i) ∧
      (∀ X j, (wordMatrix W).mulVec X (source j) = X (source j)) ∧
      (∀ X k, k ∉ Set.range dest → (wordMatrix W).mulVec X k = X k) := by
  let h := disjoint_ranges dest source hd
  exact ⟨rectangularWord dest source h M, rectangularWord_matrix dest source h M,
    rectangularWord_calls dest source h M, rectangularWord_target dest source h M,
    rectangularWord_source dest source h M, rectangularWord_untouched dest source h M⟩

lemma support_zero : support (0 : Matrix (Fin a) (Fin b) ℂ) = ∅ := by classical simp [support]

lemma rectangularWord_zero (dest : Fin a ↪ Fin r) (source : Fin b ↪ Fin r)
    (hd : ∀ i j, dest i ≠ source j) :
    rectangularWord dest source hd (0 : Matrix (Fin a) (Fin b) ℂ) = [] := by
  simp [rectangularWord, support_zero, listWord]

end
end ExactFourierCircuits.RectangularWords

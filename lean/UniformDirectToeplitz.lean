import UniformShearPreparation
import TensorWords
import OAI.Computability.FourierCircuit.GraphBlocks

/-! Literal direct lower Toeplitz fallback. Rows are visited from high to low;
all off-diagonal positions are printed, including zero coefficients. This is
an exact word construction, not a RAM producer for its prepared tables. -/
namespace ExactFourierCircuits.UniformDirectToeplitz
open OAI.ExactFourier TypedKernelWords
open scoped BigOperators
noncomputable section
variable {r : ℕ}

/-- A scalar-dependent monomial with support on precisely one coordinate. -/
def scaleMatrix (i : Fin r) (c : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.diagonal (fun j => if j = i then c else 1)

theorem scaleMatrix_monomial (i : Fin r) (c : ℂ) (hc : c ≠ 0) :
    IsMonomial (scaleMatrix i c) := by
  classical
  refine ⟨Equiv.refl _, fun j => if j = i then c else 1, ?_, ?_⟩
  · intro j; dsimp; split_ifs; exact hc; exact one_ne_zero
  · intro j k; by_cases hj : j = k <;> simp [scaleMatrix, hj]

def scaleStep (i : Fin r) (c : ℂ) (hc : c ≠ 0) : WordStep C r :=
  .monomial (scaleMatrix i c) (scaleMatrix_monomial i c hc)

theorem scaleStep_action (i : Fin r) (c : ℂ) (hc : c ≠ 0)
    (X : Fin r → ℂ) (k : Fin r) :
    (scaleStep i c hc).matrix.mulVec X k = if k = i then c * X i else X k := by
  classical
  simp only [scaleStep, WordStep.matrix, scaleMatrix, Matrix.mulVec_diagonal]
  split_ifs with h
  · subst k; rfl
  · simp

abbrev Source (i : Fin r) := {j : Fin r // j ≠ i}

def shear (i : Fin r) (j : Source i) (mu : ℂ) : List (WordStep C r) :=
  TensorWords.embeddedWord (Embedded.pair i j.val j.property.symm) (UniformLocalShear.word mu)

theorem shear_matrix (i : Fin r) (j : Source i) (mu : ℂ) :
    wordMatrix (shear i j mu) = 1 + Matrix.single i j.val mu := by
  rw [shear, TensorWords.embeddedWord_matrix, UniformLocalShear.word_matrix]
  simpa [upperShear] using Embedded.pair_matrix i j.val j.property.symm mu (0 : ℂ)

theorem shear_calls (i : Fin r) (j : Source i) (mu : ℂ) :
    wordCalls (shear i j mu) = 6 := by
  rw [shear, TensorWords.embeddedWord_calls, UniformLocalShear.word_calls]

theorem shear_length (i : Fin r) (j : Source i) (mu : ℂ) :
    (shear i j mu).length = 28 := by
  simp [shear, TensorWords.embeddedWord, UniformLocalShear.word,
    shearWord, hadamardWord]

def shearList (i : Fin r) (mu : Fin r → ℂ) (L : List (Source i)) :
    List (WordStep C r) := (L.map (fun j => shear i j (mu j.val))).flatten

theorem shearList_action (i : Fin r) (mu : Fin r → ℂ) (L : List (Source i))
    (X : Fin r → ℂ) (k : Fin r) :
    (wordMatrix (shearList i mu L)).mulVec X k =
      if k = i then X i + (L.map (fun j => mu j.val * X j.val)).sum else X k := by
  classical
  induction L generalizing X with
  | nil => simp [shearList, wordMatrix]; intro he; subst k; rfl
  | cons j L ih =>
    change (wordMatrix (shear i j (mu j.val) ++ shearList i mu L)).mulVec X k = _
    rw [wordMatrix_append, ← Matrix.mulVec_mulVec, ih, shear_matrix]
    simp only [Matrix.add_mulVec, Matrix.one_mulVec]
    have act (p : Fin r) : (Matrix.single i j.val (mu j.val)).mulVec X p =
        if p = i then mu j.val * X j.val else 0 := by
      simp [Matrix.single_mulVec, Function.update_apply]
    simp_rw [Pi.add_apply, act]
    have fixed : (L.map (fun p => mu p.val * (X p.val +
        if p.val = i then mu j.val * X j.val else 0))).sum =
        (L.map (fun p => mu p.val * X p.val)).sum := by
      congr 1
      apply List.map_congr_left
      intro p hp
      simp [p.property]
    rw [fixed]
    split_ifs with h
    · subst k; simp; ring
    · simp

theorem shearList_calls (i : Fin r) (mu : Fin r → ℂ) (L : List (Source i)) :
    wordCalls (shearList i mu L) = 6 * L.length := by
  induction L with
  | nil => simp [shearList, wordCalls]
  | cons j L ih =>
    change wordCalls (shear i j (mu j.val) ++ shearList i mu L) = _
    rw [wordCalls_append, shear_calls, ih]
    simp; omega

theorem shearList_length (i : Fin r) (mu : Fin r → ℂ) (L : List (Source i)) :
    (shearList i mu L).length = 28 * L.length := by
  induction L with
  | nil => simp [shearList]
  | cons j L ih =>
    change (shear i j (mu j.val) ++ shearList i mu L).length = _
    rw [List.length_append, shear_length, ih]
    simp; omega

/-- Computable enumeration of all lower sources; no coefficient is inspected. -/
def sources (i : Fin r) : List (Source i) :=
  List.ofFn (fun j : Fin i.val =>
    ⟨⟨j.val, Nat.lt_trans j.isLt i.isLt⟩, ne_of_lt j.isLt⟩)

@[simp] theorem sources_length (i : Fin r) : (sources i).length = i.val := by
  simp [sources]

def coefficient (h : Fin r → ℂ) (i j : Fin r) : ℂ :=
  h ⟨i.val - j.val, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

def triangular (h : Fin r → ℂ) (hr : 0 < r) (X : Fin r → ℂ) (i : Fin r) : ℂ :=
  h ⟨0, hr⟩ * X i + ∑ j : Fin i.val,
    coefficient h i ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ *
      X ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

def row (h : Fin r → ℂ) (hr : 0 < r) (h0 : h ⟨0, hr⟩ ≠ 0) (i : Fin r) :
    List (WordStep C r) :=
  [scaleStep i (h ⟨0, hr⟩) h0] ++ shearList i (coefficient h i) (sources i)

theorem row_action (h : Fin r → ℂ) (hr : 0 < r) (h0 : h ⟨0, hr⟩ ≠ 0)
    (i : Fin r) (X : Fin r → ℂ) (k : Fin r) :
    (wordMatrix (row h hr h0 i)).mulVec X k = if k = i then triangular h hr X i else X k := by
  classical
  rw [row, wordMatrix_append, ← Matrix.mulVec_mulVec, wordMatrix_singleton,
    shearList_action]
  simp_rw [scaleStep_action]
  have fixed : ((sources i).map (fun j => coefficient h i j.val *
      (if j.val = i then h ⟨0, hr⟩ * X i else X j.val))).sum =
      ((sources i).map (fun j => coefficient h i j.val * X j.val)).sum := by
    congr 1
    apply List.map_congr_left
    intro j hj
    simp [j.property]
  rw [fixed]
  have sum_eq : ((sources i).map (fun j => coefficient h i j.val * X j.val)).sum =
      ∑ j : Fin i.val, coefficient h i ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ *
        X ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ := by
    simp [sources, List.map_ofFn, List.sum_ofFn]
  rw [sum_eq]
  split_ifs <;> simp_all [triangular]

theorem row_source_original (h : Fin r → ℂ) (hr : 0 < r) (h0 : h ⟨0, hr⟩ ≠ 0)
    (i j : Fin r) (hj : j.val < i.val) (X : Fin r → ℂ) :
    (wordMatrix (row h hr h0 i)).mulVec X j = X j := by
  rw [row_action, ite_eq_right]
  intro he; subst j; omega

@[simp] theorem row_calls (h : Fin r → ℂ) (hr : 0 < r) (h0 : h ⟨0, hr⟩ ≠ 0)
    (i : Fin r) : wordCalls (row h hr h0 i) = 6 * i.val := by
  rw [row, wordCalls_append, shearList_calls, sources_length]
  simp [wordCalls, scaleStep, WordStep.calls]

@[simp] theorem row_length (h : Fin r → ℂ) (hr : 0 < r) (h0 : h ⟨0, hr⟩ ≠ 0)
    (i : Fin r) : (row h hr h0 i).length = 1 + 28 * i.val := by
  simp [row, shearList_length, add_comm]

/-- Literal chronological recursion: row k, row k-1, ..., row 0. -/
def partialWord (h : Fin r → ℂ) (hr : 0 < r) (h0 : h ⟨0, hr⟩ ≠ 0) :
    (k : ℕ) → k ≤ r → List (WordStep C r)
  | 0, _ => []
  | k + 1, hk => row h hr h0 ⟨k, by omega⟩ ++ partialWord h hr h0 k (by omega)

def word (h : Fin r → ℂ) (hr : 0 < r) (h0 : h ⟨0, hr⟩ ≠ 0) : List (WordStep C r) :=
  partialWord h hr h0 r (le_refl _)

/-- Dependence only on the target and its original lower coordinates. -/
theorem triangular_congr (h : Fin r → ℂ) (hr : 0 < r) (X Y : Fin r → ℂ)
    (i : Fin r) (same : ∀ j : Fin r, j.val ≤ i.val → X j = Y j) :
    triangular h hr X i = triangular h hr Y i := by
  unfold triangular
  rw [same i (le_refl _)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [same _ (Nat.le_of_lt j.isLt)]

/-- The descending program has processed exactly indices below k. -/
theorem partialWord_action (h : Fin r → ℂ) (hr : 0 < r) (h0 : h ⟨0, hr⟩ ≠ 0)
    (k : ℕ) (hk : k ≤ r) (X : Fin r → ℂ) (i : Fin r) :
    (wordMatrix (partialWord h hr h0 k hk)).mulVec X i =
      if i.val < k then triangular h hr X i else X i := by
  classical
  induction k generalizing X with
  | zero => simp [partialWord, wordMatrix]
  | succ k ih =>
    rw [partialWord, wordMatrix_append, ← Matrix.mulVec_mulVec, ih]
    by_cases hi : i.val < k
    · rw [ite_eq_left hi, ite_eq_left (by omega : i.val < k + 1)]
      apply triangular_congr
      intro j hj
      rw [row_action, ite_eq_right]
      intro he
      have hev := congrArg Fin.val he
      dsimp at hev
      omega
    · rw [ite_eq_right hi, row_action]
      by_cases he : i.val = k
      · have hei : i = ⟨k, by omega⟩ := Fin.ext he
        rw [ite_eq_left hei, ite_eq_left (by omega : i.val < k + 1)]
        exact congrArg (triangular h hr X) hei.symm
      · have hei : i ≠ ⟨k, by omega⟩ := by intro e; exact he (congrArg Fin.val e)
        rw [ite_eq_right hei, ite_eq_right (by omega : ¬i.val < k + 1)]

theorem word_action (h : Fin r → ℂ) (hr : 0 < r) (h0 : h ⟨0, hr⟩ ≠ 0)
    (X : Fin r → ℂ) : (wordMatrix (word h hr h0)).mulVec X = triangular h hr X := by
  funext i
  rw [word, partialWord_action, ite_eq_left i.isLt]

@[simp] theorem partialWord_calls (h : Fin r → ℂ) (hr : 0 < r)
    (h0 : h ⟨0, hr⟩ ≠ 0) (k : ℕ) (hk : k ≤ r) :
    wordCalls (partialWord h hr h0 k hk) = 6 * ∑ j ∈ Finset.range k, j := by
  induction k with
  | zero => simp [partialWord, wordCalls]
  | succ k ih =>
    rw [partialWord, wordCalls_append, row_calls, ih, Finset.sum_range_succ]
    dsimp
    ring

@[simp] theorem partialWord_length (h : Fin r → ℂ) (hr : 0 < r)
    (h0 : h ⟨0, hr⟩ ≠ 0) (k : ℕ) (hk : k ≤ r) :
    (partialWord h hr h0 k hk).length = k + 28 * ∑ j ∈ Finset.range k, j := by
  induction k with
  | zero => simp [partialWord]
  | succ k ih =>
    rw [partialWord, List.length_append, row_length, ih, Finset.sum_range_succ]
    dsimp
    ring

theorem word_calls (h : Fin r → ℂ) (hr : 0 < r) (h0 : h ⟨0, hr⟩ ≠ 0) :
    wordCalls (word h hr h0) = 3 * r * (r - 1) := by
  rw [word, partialWord_calls]
  have hs := Finset.sum_range_id_mul_two r
  calc
    6 * (∑ j ∈ Finset.range r, j) = 3 * ((∑ j ∈ Finset.range r, j) * 2) := by ring
    _ = 3 * r * (r - 1) := by rw [hs]; ring

theorem word_length (h : Fin r → ℂ) (hr : 0 < r) (h0 : h ⟨0, hr⟩ ≠ 0) :
    (word h hr h0).length = r + 14 * r * (r - 1) := by
  rw [word, partialWord_length]
  have hs := Finset.sum_range_id_mul_two r
  calc
    r + 28 * (∑ j ∈ Finset.range r, j) = r + 14 * ((∑ j ∈ Finset.range r, j) * 2) := by ring
    _ = r + 14 * r * (r - 1) := by rw [hs]; ring

theorem word_polynomial_bounds (h : Fin r → ℂ) (hr : 0 < r) (h0 : h ⟨0, hr⟩ ≠ 0) :
    wordCalls (word h hr h0) ≤ 3 * r ^ 2 ∧ (word h hr h0).length ≤ r + 14 * r ^ 2 := by
  rw [word_calls, word_length]
  have hs : r - 1 ≤ r := Nat.sub_le _ _
  constructor <;> nlinarith

theorem C_unit : IsUnit C := by
  apply (Matrix.isUnit_iff_isUnit_det C).mpr
  apply isUnit_iff_ne_zero.mpr
  have hd : C.det = Complex.I := by
    norm_num [C, a, b, Matrix.det_fin_two]
    ring
  rw [hd]
  exact Complex.I_ne_zero

theorem step_layered (s : WordStep C r) : Layered s.matrix 1 := by
  cases s with
  | monomial M hM => exact Layered.mono M (show MonomialMatrix M from hM)
  | call e =>
    simpa only [WordStep.matrix, Packing.embeddedCall_eq] using (Layered.pair C C_unit).embed e

theorem word_layered (W : List (WordStep C r)) : Layered (wordMatrix W) W.length := by
  induction W with
  | nil => simpa [wordMatrix] using (Layered.identity : Layered (1 : Matrix (Fin r) (Fin r) ℂ) 0)
  | cons s W ih =>
    rw [TensorWords.wordMatrix_cons]
    simpa [List.length_cons] using ih.mul (step_layered s)

def matrix (h : Fin r → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  fun i j => if j.val ≤ i.val then coefficient h i j else 0

theorem triangular_single (h : Fin r → ℂ) (hr : 0 < r) (i j : Fin r) :
    triangular h hr (Pi.single j 1) i = matrix h i j := by
  classical
  unfold triangular matrix
  by_cases hji : j.val < i.val
  · have jne : i ≠ j := by intro he; subst j; omega
    have jle := Nat.le_of_lt hji
    rw [ite_eq_left jle]
    simp only [Pi.single_apply, ite_eq_right jne, mul_zero, zero_add]
    let jj : Fin i.val := ⟨j.val, hji⟩
    rw [Finset.sum_eq_single jj]
    · simp [jj]
    · intro k hk hkj
      have hne : (⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ : Fin r) ≠ j := by
        intro he
        apply hkj
        apply Fin.ext
        have hev := congrArg (fun z : Fin r => z.val) he
        simpa [jj] using hev
      simp [hne]
    · simp
  · by_cases he : i = j
    · subst j
      have hs : (∑ k : Fin i.val, coefficient h i ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ *
          (Pi.single i 1 : Fin r → ℂ) ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hne : (⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ : Fin r) ≠ i := ne_of_lt k.isLt
        simp [hne]
      rw [hs]
      simp [coefficient]
    · have hnot : ¬j.val ≤ i.val := by
        intro hj
        apply he
        apply Fin.ext
        omega
      rw [ite_eq_right hnot]
      simp only [Pi.single_apply, ite_eq_right he, mul_zero, zero_add]
      apply Finset.sum_eq_zero
      intro k hk
      have hne : (⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ : Fin r) ≠ j := by
        intro heq
        have heqv := congrArg Fin.val heq
        dsimp at heqv
        have hki := k.isLt
        omega
      simp [hne]

theorem word_matrix (h : Fin r → ℂ) (hr : 0 < r) (h0 : h ⟨0, hr⟩ ≠ 0) :
    wordMatrix (word h hr h0) = matrix h := by
  ext i j
  have ha := congrFun (word_action h hr h0 (Pi.single j 1)) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, triangular_single] using ha

theorem matrix_depth (h : Fin r → ℂ) (hr : 0 < r) (h0 : h ⟨0, hr⟩ ≠ 0) :
    Layered (matrix h) (r + 14 * r * (r - 1)) := by
  have hh := word_layered (word h hr h0)
  rwa [word_matrix, word_length] at hh

theorem finite_fallback_bounds (h : Fin r → ℂ) (hr : 0 < r) (h0 : h ⟨0, hr⟩ ≠ 0)
    (cap : r ≤ 195) : wordCalls (word h hr h0) ≤ 114075 ∧
      Layered (matrix h) 532545 := by
  have hb := word_polynomial_bounds h hr h0
  have hs : r - 1 ≤ r := Nat.sub_le _ _
  constructor
  · nlinarith
  · apply (matrix_depth h hr h0).weaken
    nlinarith

def oneCoordinate (i : Fin r) : Fin 1 ↪ Fin r where
  toFun := fun _ => i
  inj' := fun _ _ _ => Subsingleton.elim _ _

@[simp] theorem oneCoordinate_apply (i : Fin r) (j : Fin 1) : oneCoordinate i j = i := rfl

/-- Each diagonal scaling is an actual embedded width-one operation. -/
theorem scale_width_one (i : Fin r) (c : ℂ) :
    scaleMatrix i c = Embedded.matrix (oneCoordinate i) (fun _ _ : Fin 1 => c) := by
  classical
  ext j k
  by_cases hj : j = i
  · subst j
    by_cases hk : k = i
    · subst k
      have he := Embedded.matrix_on (oneCoordinate i) (fun _ _ : Fin 1 => c) 0 0
      simpa [scaleMatrix] using he.symm
    · have hn : k ∉ Set.range (oneCoordinate i) := by
        rintro ⟨a, ha⟩
        exact hk ha.symm
      calc
        scaleMatrix i c i k = if i = k then 1 else 0 := by
          have hik : i ≠ k := fun he => hk he.symm
          simp [scaleMatrix, hik]
        _ = Embedded.matrix (oneCoordinate i) (fun _ _ : Fin 1 => c) i k :=
          (Embedded.matrix_off_col (oneCoordinate i) (fun _ _ : Fin 1 => c) i k hn).symm
  · have hn : j ∉ Set.range (oneCoordinate i) := by
      rintro ⟨a, ha⟩
      exact hj ha.symm
    calc
      scaleMatrix i c j k = if j = k then 1 else 0 := by
        rcases eq_or_ne j k with rfl | he
        · simp [scaleMatrix, hj]
        · simp [scaleMatrix, he]
      _ = Embedded.matrix (oneCoordinate i) (fun _ _ : Fin 1 => c) j k :=
        (Embedded.matrix_off_row (oneCoordinate i) (fun _ _ : Fin 1 => c) j k hn).symm

end

variable {r : ℕ}

/-- Literal topology and coefficient references are computable and independent of h. -/
inductive Operation (r : ℕ) where
  | scale (target : Fin r)
  | shear (target : Fin r) (source : Fin target.val)
  deriving DecidableEq

def rowTopology (i : Fin r) : List (Operation r) :=
  .scale i :: List.ofFn (fun j : Fin i.val => .shear i j)

def partialTopology : (k : ℕ) → k ≤ r → List (Operation r)
  | 0, _ => []
  | k + 1, hk => rowTopology ⟨k, by omega⟩ ++ partialTopology k (by omega)

def topology (r : ℕ) : List (Operation r) := partialTopology r (le_refl _)

def coefficientIndex : Operation r → Fin r
  | .scale _ => ⟨0, by rename_i i; exact Nat.zero_lt_of_lt i.isLt⟩
  | .shear i j => ⟨i.val - j.val, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

@[simp] theorem partialTopology_length (k : ℕ) (hk : k ≤ r) :
    (partialTopology k hk).length = k + ∑ j ∈ Finset.range k, j := by
  induction k with
  | zero => simp [partialTopology]
  | succ k ih =>
    simp only [partialTopology, List.length_append, rowTopology, List.length_cons,
      List.length_ofFn, ih, Finset.sum_range_succ]
    omega

theorem topology_length (r : ℕ) : (topology r).length = r + r * (r - 1) / 2 := by
  rw [topology, partialTopology_length, Finset.sum_range_id]

@[simp] theorem topology_empty : topology 0 = [] := rfl

noncomputable section
open UniformScalarPreparation

def render (h : Fin r → ℂ) (hr : 0 < r) (h0 : h ⟨0, hr⟩ ≠ 0) :
    Operation r → List (WordStep C r)
  | .scale i => [scaleStep i (h ⟨0, hr⟩) h0]
  | .shear i j => shear i
      ⟨⟨j.val, Nat.lt_trans j.isLt i.isLt⟩, ne_of_lt j.isLt⟩
      (coefficient h i ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩)

theorem render_rowTopology (h : Fin r → ℂ) (hr : 0 < r) (h0 : h ⟨0, hr⟩ ≠ 0)
    (i : Fin r) : ((rowTopology i).map (render h hr h0)).flatten = row h hr h0 i := by
  simp [rowTopology, render, row, shearList, sources, List.map_ofFn, Function.comp_def]

theorem render_partialTopology (h : Fin r → ℂ) (hr : 0 < r) (h0 : h ⟨0, hr⟩ ≠ 0)
    (k : ℕ) (hk : k ≤ r) :
    ((partialTopology k hk).map (render h hr h0)).flatten = partialWord h hr h0 k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [partialTopology, List.map_append, List.flatten_append,
      render_rowTopology, ih, partialWord]

theorem render_topology (h : Fin r → ℂ) (hr : 0 < r) (h0 : h ⟨0, hr⟩ ≠ 0) :
    ((topology r).map (render h hr h0)).flatten = word h hr h0 :=
  render_partialTopology h hr h0 r (le_refl _)

/-- One shared coefficient/scales bank, not one DAG copy per row or entry. -/
def coefficientBank {b : ℕ} (d : DAG b r) : DAG b (r * 8) :=
  UniformShearPreparation.table d

def references {b : ℕ} (d : DAG b r) (op : Operation r) (q : Fin 8) :
    Fin (coefficientBank d).length :=
  (coefficientBank d).output (finProdFinEquiv (coefficientIndex op, q))

/-- The reference schema carries all eight shared scalars for each operation. -/
def referenceRows {b : ℕ} (d : DAG b r) : List (Fin 8 → Fin (coefficientBank d).length) :=
  (topology r).map (references d)

theorem references_value {b : ℕ} (d : DAG b r) (roots : Fin b → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) (op : Operation r) (q : Fin 8) :
    (coefficientBank d).program.run roots (UniformShearPreparation.table_admissible d roots unit hd)
      (references d op q) =
      UniformShearPreparation.expected (d.run roots hd (coefficientIndex op)) q := by
  exact UniformShearPreparation.table_run d roots unit hd (coefficientIndex op) q

theorem references_coefficient {b : ℕ} (d : DAG b r) (roots : Fin b → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) (op : Operation r) :
    (coefficientBank d).program.run roots (UniformShearPreparation.table_admissible d roots unit hd)
      (references d op 0) = d.run roots hd (coefficientIndex op) := by
  rw [references_value d roots unit hd op (0 : Fin 8)]
  rfl

theorem references_scales {b : ℕ} (d : DAG b r) (roots : Fin b → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) (op : Operation r) (q : Fin 6) :
    (coefficientBank d).program.run roots (UniformShearPreparation.table_admissible d roots unit hd)
      (references d op ⟨q.val + 2, by omega⟩) =
      UniformShearPreparation.scaleValues d roots unit hd (coefficientIndex op) q := by
  rw [references_value d roots unit hd op ⟨q.val + 2, by omega⟩,
    UniformShearPreparation.scaleValues_eq d roots unit hd (coefficientIndex op) q]
  fin_cases q <;> rfl

/-- Values in every varying diagonal come from the shared supplied-root replay bank. -/
def preparedRender {b : ℕ} (d : DAG b r) (roots : Fin b → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) (hr : 0 < r)
    (h0 : d.run roots hd ⟨0, hr⟩ ≠ 0) : Operation r → List (WordStep C r)
  | .scale i => [scaleStep i (d.run roots hd ⟨0, hr⟩) h0]
  | .shear i j => TensorWords.embeddedWord
      (Embedded.pair i ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ (Ne.symm (ne_of_lt j.isLt)))
      (UniformShearPreparation.preparedWord d roots unit hd (coefficientIndex (.shear i j)))

theorem preparedRender_eq {b : ℕ} (d : DAG b r) (roots : Fin b → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) (hr : 0 < r)
    (h0 : d.run roots hd ⟨0, hr⟩ ≠ 0) (op : Operation r) :
    preparedRender d roots unit hd hr h0 op = render (d.run roots hd) hr h0 op := by
  cases op with
  | scale i => rfl
  | shear i j =>
    simp only [preparedRender, UniformShearPreparation.preparedWord_eq]
    rfl

def preparedWord {b : ℕ} (d : DAG b r) (roots : Fin b → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) (hr : 0 < r)
    (h0 : d.run roots hd ⟨0, hr⟩ ≠ 0) : List (WordStep C r) :=
  ((topology r).map (preparedRender d roots unit hd hr h0)).flatten

theorem preparedWord_eq {b : ℕ} (d : DAG b r) (roots : Fin b → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) (hr : 0 < r)
    (h0 : d.run roots hd ⟨0, hr⟩ ≠ 0) :
    preparedWord d roots unit hd hr h0 = word (d.run roots hd) hr h0 := by
  unfold preparedWord
  have hf : preparedRender d roots unit hd hr h0 = render (d.run roots hd) hr h0 :=
    funext (preparedRender_eq d roots unit hd hr h0)
  rw [hf]
  exact render_topology _ _ _

theorem preparedWord_matrix {b : ℕ} (d : DAG b r) (roots : Fin b → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) (hr : 0 < r)
    (h0 : d.run roots hd ⟨0, hr⟩ ≠ 0) :
    wordMatrix (preparedWord d roots unit hd hr h0) = matrix (d.run roots hd) := by
  rw [preparedWord_eq, word_matrix]

theorem preparedWord_calls {b : ℕ} (d : DAG b r) (roots : Fin b → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) (hr : 0 < r)
    (h0 : d.run roots hd ⟨0, hr⟩ ≠ 0) :
    wordCalls (preparedWord d roots unit hd hr h0) = 3 * r * (r - 1) := by
  rw [preparedWord_eq, word_calls]

theorem preparedWord_action {b : ℕ} (d : DAG b r) (roots : Fin b → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) (hr : 0 < r)
    (h0 : d.run roots hd ⟨0, hr⟩ ≠ 0) (X : Fin r → ℂ) :
    (wordMatrix (preparedWord d roots unit hd hr h0)).mulVec X = triangular (d.run roots hd) hr X := by
  rw [preparedWord_eq, word_action]

theorem preparedWord_length {b : ℕ} (d : DAG b r) (roots : Fin b → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) (hr : 0 < r)
    (h0 : d.run roots hd ⟨0, hr⟩ ≠ 0) :
    (preparedWord d roots unit hd hr h0).length = r + 14 * r * (r - 1) := by
  rw [preparedWord_eq, word_length]

theorem referenceRows_length {b : ℕ} (d : DAG b r) :
    (referenceRows d).length = r + r * (r - 1) / 2 := by
  simp [referenceRows, topology_length]

theorem references_bound {b : ℕ} (d : DAG b r) (op : Operation r) (q : Fin 8) :
    (references d op q).val < 7 * (d.length + b + r + 1) :=
  (references d op q).isLt.trans_le (UniformShearPreparation.table_length_bound d)

theorem bank_admissible {b : ℕ} (d : DAG b r) (roots : Fin b → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) :
    (coefficientBank d).Admissible roots := UniformShearPreparation.table_admissible d roots unit hd

theorem bank_size {b : ℕ} (d : DAG b r) :
    (coefficientBank d).length = 2 * d.length + 2 * b + 7 * r + 4 :=
  UniformShearPreparation.table_length d

theorem bank_rootReads {b : ℕ} (d : DAG b r) :
    UniformShearPreparation.programCount .rootRead (coefficientBank d).program =
      UniformShearPreparation.programCount .rootRead d.program + b :=
  UniformShearPreparation.table_rootReads d

end
end ExactFourierCircuits.UniformDirectToeplitz

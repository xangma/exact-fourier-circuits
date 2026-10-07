import TypedKernelWords
import BinaryFrames
import OAI.Computability.FourierCircuit.LiveSectors

/- Exact disjoint-pair compilation on explicitly identified binary addresses. -/
namespace ExactFourierCircuits.DirectionalWords
noncomputable section
open OAI.ExactFourier
open scoped BigOperators

abbrev Bits (n : ℕ) := Fin n → ZMod 2

lemma binary_values (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

@[simp] theorem bits_add_self {n : ℕ} (z : Bits n) : z + z = 0 := by
  ext p
  exact CharTwo.add_self_eq_zero (z p)

theorem exists_pivot {n : ℕ} (z : Bits n) (hz : z ≠ 0) : ∃ p, z p = 1 := by
  by_contra h
  apply hz
  ext p
  exact (binary_values (z p)).resolve_right (fun hp => h ⟨p, hp⟩)

abbrev Representatives {n : ℕ} (p : Fin n) := {x : Bits n // x p = 0}

def pairPoint {n : ℕ} (z : Bits n) (p : Fin n)
    (u : Σ _ : Representatives p, Fin 2) : Bits n :=
  if u.2 = 0 then u.1.val else u.1.val + z

theorem pairPoint_injective {n : ℕ} (z : Bits n) (p : Fin n) (hp : z p = 1) :
    Function.Injective (pairPoint z p) := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  fin_cases i <;> fin_cases j
  · have hxy : x = y := Subtype.ext (by simpa [pairPoint] using h)
    cases hxy
    rfl
  · have he := congrFun h p
    simp [pairPoint, x.property, y.property, hp] at he
  · have he := congrFun h p
    simp [pairPoint, x.property, y.property, hp] at he
  · have hxy : x = y := Subtype.ext (by simpa [pairPoint] using h)
    cases hxy
    rfl

theorem pairPoint_surjective {n : ℕ} (z : Bits n) (p : Fin n) (hp : z p = 1) :
    Function.Surjective (pairPoint z p) := by
  intro x
  by_cases hx : x p = 0
  · exact ⟨⟨⟨x, hx⟩, 0⟩, by simp [pairPoint]⟩
  · have hx1 : x p = 1 := (binary_values (x p)).resolve_left hx
    refine ⟨⟨⟨x + z, ?_⟩, 1⟩, ?_⟩
    · simp [hx1, hp, CharTwo.add_self_eq_zero]
    · simp [pairPoint, add_assoc]

def pairEquiv {n : ℕ} (z : Bits n) (p : Fin n) (hp : z p = 1) :
    (Σ _ : Representatives p, Fin 2) ≃ Bits n :=
  Equiv.ofBijective (pairPoint z p)
    ⟨pairPoint_injective z p hp, pairPoint_surjective z p hp⟩

@[simp] theorem pairEquiv_apply {n : ℕ} (z : Bits n) (p : Fin n)
    (hp : z p = 1) (x : Σ _ : Representatives p, Fin 2) :
    pairEquiv z p hp x = pairPoint z p x := rfl

theorem representatives_card {n : ℕ} (hn : 1 ≤ n) (z : Bits n)
    (p : Fin n) (hp : z p = 1) : Fintype.card (Representatives p) = 2 ^ (n - 1) := by
  have h := Fintype.card_congr (pairEquiv z p hp)
  have he : Fintype.card (Representatives p) * 2 = 2 ^ n := by
    simpa [Bits, Fintype.card_sigma, ZMod.card] using h
  have hn' : n = (n - 1) + 1 := by omega
  have hpow : 2 ^ n = 2 ^ (n - 1) * 2 := by
    conv_lhs => rw [hn', pow_succ]
  rw [hpow] at he
  omega

/-- This equivalence is explicit but is not asserted to use Python's bit order. -/
def addresses (n : ℕ) : Bits n ≃ Fin (2 ^ n) :=
  (Fintype.equivFin (Bits n)).trans (Equiv.cast (by simp [Bits, ZMod.card]))

def translationEquiv {n : ℕ} (z : Bits n) : Equiv.Perm (Bits n) where
  toFun x := x + z
  invFun x := x + z
  left_inv x := by simp [add_assoc]
  right_inv x := by simp [add_assoc]

def translation {n : ℕ} (z : Bits n) : Matrix (Bits n) (Bits n) ℂ :=
  permM (translationEquiv z)

def directionalMatrix {n : ℕ} (z : Bits n) : Matrix (Bits n) (Bits n) ℂ :=
  a • (1 : Matrix (Bits n) (Bits n) ℂ) + b • translation z

def directionalC {n : ℕ} (z : Bits n) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.reindex (addresses n) (addresses n) (directionalMatrix z)

def translationFin {n : ℕ} (z : Bits n) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.reindex (addresses n) (addresses n) (translation z)

lemma pairPoint_translation {n : ℕ} (z : Bits n) (p : Fin n)
    (x : Representatives p) (i : Fin 2) :
    pairPoint z p ⟨x, i⟩ + z = pairPoint z p ⟨x, Equiv.swap 0 1 i⟩ := by
  fin_cases i <;> simp [pairPoint, add_assoc]

theorem blocks_directional {n : ℕ} (z : Bits n) (p : Fin n) (hp : z p = 1) :
    Matrix.reindex (pairEquiv z p hp) (pairEquiv z p hp)
      (Matrix.blockDiagonal' (fun _ : Representatives p => C)) = directionalMatrix z := by
  classical
  ext u v
  obtain ⟨⟨x, i⟩, rfl⟩ := (pairEquiv z p hp).surjective u
  obtain ⟨⟨y, j⟩, rfl⟩ := (pairEquiv z p hp).surjective v
  have he : pairEquiv z p hp ⟨x, i⟩ = pairEquiv z p hp ⟨y, j⟩ ↔ x = y ∧ i = j := by
    rw [(pairEquiv z p hp).injective.eq_iff]
    simp
  have ht : pairEquiv z p hp ⟨x, i⟩ = translationEquiv z (pairEquiv z p hp ⟨y, j⟩) ↔
      x = y ∧ i = Equiv.swap 0 1 j := by
    change pairEquiv z p hp ⟨x, i⟩ = pairPoint z p ⟨y, j⟩ + z ↔ _
    rw [pairPoint_translation]
    change pairEquiv z p hp ⟨x, i⟩ = pairEquiv z p hp ⟨y, Equiv.swap 0 1 j⟩ ↔ _
    rw [(pairEquiv z p hp).injective.eq_iff]
    simp
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    directionalMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, translation, permM, he, ht]
  by_cases hxy : x = y
  · subst y
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.blockDiagonal'_apply, C]
  · simp [Matrix.blockDiagonal'_apply, hxy]

def pairCoordinates {n : ℕ} (z : Bits n) (p : Fin n) (hp : z p = 1) :
    (Σ _ : Representatives p, Fin 2) ≃ Fin (2 ^ n) :=
  (pairEquiv z p hp).trans (addresses n)

def callEmbedding {n : ℕ} (z : Bits n) (p : Fin n) (hp : z p = 1)
    (x : Representatives p) : Fin 2 ↪ Fin (2 ^ n) :=
  (Embedded.sigmaIn x).trans (pairCoordinates z p hp).toEmbedding

/-- Disjoint calls are stored in reverse enumeration order because wordMatrix reverses the list. -/
def directionalWordAt {n : ℕ} (z : Bits n) (p : Fin n) (hp : z p = 1) :
    List (WordStep C (2 ^ n)) :=
  (Finset.univ.toList.map (fun x : Representatives p =>
    WordStep.call (callEmbedding z p hp x))).reverse

theorem directionalWordAt_calls {n : ℕ} (hn : 1 ≤ n) (z : Bits n)
    (p : Fin n) (hp : z p = 1) : wordCalls (directionalWordAt z p hp) = 2 ^ (n - 1) := by
  simpa [directionalWordAt, wordCalls, WordStep.calls, List.map_reverse, List.map_map,
    Function.comp_def] using representatives_card hn z p hp

theorem directionalWordAt_matrix {n : ℕ} (z : Bits n) (p : Fin n) (hp : z p = 1) :
    wordMatrix (directionalWordAt z p hp) = directionalC z := by
  classical
  have hc (x : Representatives p) : embeddedCall C (callEmbedding z p hp x) =
      Matrix.reindex (pairCoordinates z p hp) (pairCoordinates z p hp)
        (Embedded.matrix (Embedded.sigmaIn x) C) := by
    rw [Packing.embeddedCall_eq, callEmbedding, ← Embedded.matrix_comp, Embedded.matrix_equiv]
  simp only [directionalWordAt, wordMatrix, List.map_reverse, List.reverse_reverse,
    List.map_map, Function.comp_def, WordStep.matrix, hc]
  rw [show Finset.univ.toList.map (fun x : Representatives p =>
      Matrix.reindex (pairCoordinates z p hp) (pairCoordinates z p hp)
        (Embedded.matrix (Embedded.sigmaIn x) C)) =
      (Finset.univ.toList.map (fun x : Representatives p => Embedded.matrix (Embedded.sigmaIn x) C)).map
        (Matrix.reindexAlgEquiv ℂ ℂ (pairCoordinates z p hp)).toMonoidHom
      from (List.map_map ..).symm]
  rw [← map_list_prod, Embedded.blockDiagonal'_product]
  change Matrix.reindex (pairCoordinates z p hp) (pairCoordinates z p hp)
    (Matrix.blockDiagonal' (fun _ : Representatives p => C)) = directionalC z
  change Matrix.reindex (addresses n) (addresses n)
    (Matrix.reindex (pairEquiv z p hp) (pairEquiv z p hp)
      (Matrix.blockDiagonal' (fun _ : Representatives p => C))) = directionalC z
  rw [blocks_directional]
  rfl

def directionalWord {n : ℕ} (z : Bits n) (hz : z ≠ 0) : List (WordStep C (2 ^ n)) :=
  directionalWordAt z (Classical.choose (exists_pivot z hz))
    (Classical.choose_spec (exists_pivot z hz))

theorem compile_directional {n : ℕ} (hn : 1 ≤ n) (z : Bits n) (hz : z ≠ 0) :
    ∃ W : List (WordStep C (2 ^ n)),
      wordMatrix W = directionalC z ∧ wordCalls W = 2 ^ (n - 1) := by
  refine ⟨directionalWord z hz, directionalWordAt_matrix _ _ _, ?_⟩
  exact directionalWordAt_calls hn _ _ _

theorem blocks_translation {n : ℕ} (z : Bits n) (p : Fin n) (hp : z p = 1) :
    Matrix.reindex (pairEquiv z p hp) (pairEquiv z p hp)
      (Matrix.blockDiagonal' (fun _ : Representatives p => swap)) = translation z := by
  classical
  ext u v
  obtain ⟨⟨x, i⟩, rfl⟩ := (pairEquiv z p hp).surjective u
  obtain ⟨⟨y, j⟩, rfl⟩ := (pairEquiv z p hp).surjective v
  have ht : pairEquiv z p hp ⟨x, i⟩ = translationEquiv z (pairEquiv z p hp ⟨y, j⟩) ↔
      x = y ∧ i = Equiv.swap 0 1 j := by
    change pairEquiv z p hp ⟨x, i⟩ = pairPoint z p ⟨y, j⟩ + z ↔ _
    rw [pairPoint_translation]
    change pairEquiv z p hp ⟨x, i⟩ = pairEquiv z p hp ⟨y, Equiv.swap 0 1 j⟩ ↔ _
    rw [(pairEquiv z p hp).injective.eq_iff]
    simp
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    translation, permM, ht]
  by_cases hxy : x = y
  · subst y
    fin_cases i <;> fin_cases j <;> simp [Matrix.blockDiagonal'_apply, swap]
  · simp [Matrix.blockDiagonal'_apply, hxy]

theorem directionalMatrix_square {n : ℕ} (z : Bits n) (p : Fin n) (hp : z p = 1) :
    directionalMatrix z * directionalMatrix z = translation z := by
  let e := pairEquiv z p hp
  let B := Matrix.blockDiagonal' (fun _ : Representatives p => C)
  calc
    directionalMatrix z * directionalMatrix z = Matrix.reindex e e (B * B) := by
      rw [← blocks_directional z p hp]
      exact ((Matrix.reindexAlgEquiv ℂ ℂ e).map_mul B B).symm
    _ = Matrix.reindex e e (Matrix.blockDiagonal' (fun _ : Representatives p => swap)) := by
      simp only [B, ← Matrix.blockDiagonal'_mul, C_square]
    _ = translation z := blocks_translation z p hp

theorem translation_square {n : ℕ} (z : Bits n) : translation z * translation z = 1 := by
  ext x y
  simp [translation, permM_mul_apply, permM, translationEquiv, Matrix.one_apply]

theorem directionalC_square {n : ℕ} (z : Bits n) (p : Fin n) (hp : z p = 1) :
    directionalC z * directionalC z = translationFin z := by
  change (Matrix.reindexAlgEquiv ℂ ℂ (addresses n)) (directionalMatrix z) *
      (Matrix.reindexAlgEquiv ℂ ℂ (addresses n)) (directionalMatrix z) =
    (Matrix.reindexAlgEquiv ℂ ℂ (addresses n)) (translation z)
  rw [← map_mul, directionalMatrix_square z p hp]

theorem translationFin_square {n : ℕ} (z : Bits n) : translationFin z * translationFin z = 1 := by
  change (Matrix.reindexAlgEquiv ℂ ℂ (addresses n)) (translation z) *
      (Matrix.reindexAlgEquiv ℂ ℂ (addresses n)) (translation z) = 1
  rw [← map_mul, translation_square, map_one]

theorem translationFin_isMonomial {n : ℕ} (z : Bits n) : IsMonomial (translationFin z) :=
  (permM_monomial (translationEquiv z)).reindex (addresses n)

theorem directionalC_inverse {n : ℕ} (z : Bits n) (p : Fin n) (hp : z p = 1) :
    (directionalC z)⁻¹ = translationFin z * directionalC z := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, directionalC_square z p hp, translationFin_square]

/-- Every inverse layer is still compiled from forward calls, followed by one monomial. -/
def inverseDirectionalWordAt {n : ℕ} (z : Bits n) (p : Fin n) (hp : z p = 1) :
    List (WordStep C (2 ^ n)) :=
  directionalWordAt z p hp ++ [.monomial (translationFin z) (translationFin_isMonomial z)]

theorem inverseDirectionalWordAt_matrix {n : ℕ} (z : Bits n) (p : Fin n) (hp : z p = 1) :
    wordMatrix (inverseDirectionalWordAt z p hp) = (directionalC z)⁻¹ := by
  simp only [inverseDirectionalWordAt, TypedKernelWords.wordMatrix_append,
    TypedKernelWords.wordMatrix_singleton, WordStep.matrix, directionalWordAt_matrix]
  exact (directionalC_inverse z p hp).symm

theorem inverseDirectionalWordAt_calls {n : ℕ} (hn : 1 ≤ n) (z : Bits n)
    (p : Fin n) (hp : z p = 1) :
    wordCalls (inverseDirectionalWordAt z p hp) = 2 ^ (n - 1) := by
  rw [inverseDirectionalWordAt, TypedKernelWords.wordCalls_append,
    directionalWordAt_calls hn z p hp]
  simp [wordCalls, WordStep.calls]

def inverseDirectionalWord {n : ℕ} (z : Bits n) (hz : z ≠ 0) :
    List (WordStep C (2 ^ n)) :=
  inverseDirectionalWordAt z (Classical.choose (exists_pivot z hz))
    (Classical.choose_spec (exists_pivot z hz))

theorem compile_inverse_directional {n : ℕ} (hn : 1 ≤ n) (z : Bits n) (hz : z ≠ 0) :
    ∃ W : List (WordStep C (2 ^ n)),
      wordMatrix W = (directionalC z)⁻¹ ∧ wordCalls W = 2 ^ (n - 1) := by
  refine ⟨inverseDirectionalWord z hz, inverseDirectionalWordAt_matrix _ _ _, ?_⟩
  exact inverseDirectionalWordAt_calls hn _ _ _

end
end ExactFourierCircuits.DirectionalWords

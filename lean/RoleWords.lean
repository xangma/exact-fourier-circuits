import TensorWords
import OAI.Computability.FourierCircuit.MatrixRelabel

namespace ExactFourierCircuits.RoleWords
noncomputable section
open OAI.ExactFourier
open scoped BigOperators

/-- Role is the outer coordinate, address the inner coordinate. -/
def roleAddresses (r n : ℕ) : (Fin r × Fin (2 ^ n)) ≃ Fin (r * 2 ^ n) :=
  finProdFinEquiv

theorem roleAddresses_val (r n : ℕ) (i : Fin r) (a : Fin (2 ^ n)) :
    (roleAddresses r n (i, a)).val = i.val * 2 ^ n + a.val := by
  simp [roleAddresses, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

def copyCoordinates (r n : ℕ) : (Σ _ : Fin (2 ^ n), Fin r) ≃ Fin (r * 2 ^ n) :=
  (Equiv.sigmaEquivProd (Fin (2 ^ n)) (Fin r)).trans
    ((Equiv.prodComm _ _).trans (roleAddresses r n))

def pointwiseMatrix {r : ℕ} (n : ℕ) (M : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin (r * 2 ^ n)) (Fin (r * 2 ^ n)) ℂ :=
  Matrix.reindex (roleAddresses r n) (roleAddresses r n)
    (Matrix.kronecker M (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ))

def pointwiseWord {r : ℕ} (n : ℕ) (W : List (WordStep C r)) :
    List (WordStep C (r * 2 ^ n)) :=
  TensorWords.parallelWord (copyCoordinates r n) W

theorem pointwiseWord_matrix {r : ℕ} (n : ℕ) (W : List (WordStep C r)) :
    wordMatrix (pointwiseWord n W) = pointwiseMatrix n (wordMatrix W) := by
  rw [pointwiseWord, TensorWords.parallelWord_matrix]
  ext i j
  obtain ⟨⟨i, a⟩, rfl⟩ := (roleAddresses r n).surjective i
  obtain ⟨⟨j, b⟩, rfl⟩ := (roleAddresses r n).surjective j
  simp [pointwiseMatrix, Matrix.reindex_apply, copyCoordinates,
    Matrix.blockDiagonal'_apply, Matrix.one_apply]

theorem pointwiseWord_calls {r : ℕ} (n : ℕ) (W : List (WordStep C r)) :
    wordCalls (pointwiseWord n W) = 2 ^ n * wordCalls W :=
  TensorWords.parallelWord_calls (copyCoordinates r n) W

def arrayValues {r : ℕ} (n : ℕ) (X : Fin r → Fin (2 ^ n) → ℂ) : Fin (r * 2 ^ n) → ℂ :=
  fun i => X ((roleAddresses r n).symm i).1 ((roleAddresses r n).symm i).2

@[simp] theorem arrayValues_at {r : ℕ} (n : ℕ) (X : Fin r → Fin (2 ^ n) → ℂ)
    (i : Fin r) (a : Fin (2 ^ n)) : arrayValues n X (roleAddresses r n (i, a)) = X i a := by
  simp [arrayValues]

theorem pointwiseMatrix_apply {r : ℕ} (n : ℕ) (M : Matrix (Fin r) (Fin r) ℂ)
    (X : Fin r → Fin (2 ^ n) → ℂ) (i : Fin r) (a : Fin (2 ^ n)) :
    (pointwiseMatrix n M).mulVec (arrayValues n X) (roleAddresses r n (i, a)) =
      M.mulVec (fun j => X j a) i := by
  rw [pointwiseMatrix, reindex_mulVec]
  simp [arrayValues, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.one_apply]

theorem pointwiseWord_apply {r : ℕ} (n : ℕ) (W : List (WordStep C r))
    (X : Fin r → Fin (2 ^ n) → ℂ) (i : Fin r) (a : Fin (2 ^ n)) :
    (wordMatrix (pointwiseWord n W)).mulVec (arrayValues n X) (roleAddresses r n (i, a)) =
      (wordMatrix W).mulVec (fun j => X j a) i := by
  rw [pointwiseWord_matrix, pointwiseMatrix_apply]

theorem pointwiseWord_array {r : ℕ} (n : ℕ) (W : List (WordStep C r))
    (X : Fin r → Fin (2 ^ n) → ℂ) :
    (wordMatrix (pointwiseWord n W)).mulVec (arrayValues n X) =
      arrayValues n (fun i a => (wordMatrix W).mulVec (fun j => X j a) i) := by
  funext k
  obtain ⟨⟨i, a⟩, rfl⟩ := (roleAddresses r n).surjective k
  rw [pointwiseWord_apply, arrayValues_at]

def pointwiseStepWord {r : ℕ} (n : ℕ) (s : WordStep C r) :
    List (WordStep C (r * 2 ^ n)) := pointwiseWord n [s]

theorem pointwiseStepWord_matrix {r : ℕ} (n : ℕ) (s : WordStep C r) :
    wordMatrix (pointwiseStepWord n s) = pointwiseMatrix n s.matrix := by
  rw [pointwiseStepWord, pointwiseWord_matrix, TypedKernelWords.wordMatrix_singleton]

theorem pointwiseStepWord_calls {r : ℕ} (n : ℕ) (s : WordStep C r) :
    wordCalls (pointwiseStepWord n s) = 2 ^ n * s.calls := by
  rw [pointwiseStepWord, pointwiseWord_calls]
  simp [wordCalls]

def roleShearWord {r : ℕ} (dest source : Fin r) (hds : dest ≠ source)
    (t : ℂ) (ht : t ≠ 0) : List (WordStep C r) :=
  TensorWords.embeddedWord (Embedded.pair dest source hds) (TypedKernelWords.shearWord t ht)

theorem roleShearWord_matrix {r : ℕ} (dest source : Fin r) (hds : dest ≠ source)
    (t : ℂ) (ht : t ≠ 0) :
    wordMatrix (roleShearWord dest source hds t ht) = 1 + Matrix.single dest source t := by
  rw [roleShearWord, TensorWords.embeddedWord_matrix, TypedKernelWords.shearWord_matrix]
  simpa [upperShear] using Embedded.pair_matrix dest source hds t (0 : ℂ)

theorem roleShearWord_calls {r : ℕ} (dest source : Fin r) (hds : dest ≠ source)
    (t : ℂ) (ht : t ≠ 0) : wordCalls (roleShearWord dest source hds t ht) = 3 := by
  rw [roleShearWord, TensorWords.embeddedWord_calls, TypedKernelWords.shearWord_calls]

def pointwiseShearWord {r : ℕ} (n : ℕ) (dest source : Fin r) (hds : dest ≠ source)
    (t : ℂ) (ht : t ≠ 0) : List (WordStep C (r * 2 ^ n)) :=
  pointwiseWord n (roleShearWord dest source hds t ht)

theorem pointwiseShearWord_matrix {r : ℕ} (n : ℕ) (dest source : Fin r) (hds : dest ≠ source)
    (t : ℂ) (ht : t ≠ 0) :
    wordMatrix (pointwiseShearWord n dest source hds t ht) =
      pointwiseMatrix n (1 + Matrix.single dest source t) := by
  rw [pointwiseShearWord, pointwiseWord_matrix, roleShearWord_matrix]

theorem pointwiseShearWord_calls {r : ℕ} (n : ℕ) (dest source : Fin r) (hds : dest ≠ source)
    (t : ℂ) (ht : t ≠ 0) :
    wordCalls (pointwiseShearWord n dest source hds t ht) = 3 * 2 ^ n := by
  rw [pointwiseShearWord, pointwiseWord_calls, roleShearWord_calls, Nat.mul_comm]

theorem pointwiseShearWord_apply {r : ℕ} (n : ℕ) (dest source : Fin r) (hds : dest ≠ source)
    (t : ℂ) (ht : t ≠ 0) (X : Fin r → Fin (2 ^ n) → ℂ)
    (i : Fin r) (a : Fin (2 ^ n)) :
    (wordMatrix (pointwiseShearWord n dest source hds t ht)).mulVec (arrayValues n X)
      (roleAddresses r n (i, a)) = X i a + if i = dest then t * X source a else 0 := by
  rw [pointwiseShearWord_matrix, pointwiseMatrix_apply, Matrix.add_mulVec, Matrix.one_mulVec]
  simp [Matrix.single_mulVec, Function.update_apply, eq_comm]

theorem pointwiseShearWord_untouched {r : ℕ} (n : ℕ) (dest source : Fin r) (hds : dest ≠ source)
    (t : ℂ) (ht : t ≠ 0) (X : Fin r → Fin (2 ^ n) → ℂ)
    (i : Fin r) (hi : i ≠ dest) (a : Fin (2 ^ n)) :
    (wordMatrix (pointwiseShearWord n dest source hds t ht)).mulVec (arrayValues n X)
      (roleAddresses r n (i, a)) = X i a := by
  rw [pointwiseShearWord_apply]
  simp [hi]

theorem compile_pointwise_shear {r : ℕ} (n : ℕ) (dest source : Fin r) (hds : dest ≠ source)
    (t : ℂ) (ht : t ≠ 0) :
    ∃ W : List (WordStep C (r * 2 ^ n)),
      wordMatrix W = pointwiseMatrix n (1 + Matrix.single dest source t) ∧
      wordCalls W = 3 * 2 ^ n :=
  ⟨pointwiseShearWord n dest source hds t ht,
    pointwiseShearWord_matrix n dest source hds t ht,
    pointwiseShearWord_calls n dest source hds t ht⟩

end
end ExactFourierCircuits.RoleWords

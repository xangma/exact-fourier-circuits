import KernelIdentities
import OAI.Computability.FourierCircuit.Words

/- Literal forward-call words, with proofs in the upstream WordStep semantics. -/
namespace ExactFourierCircuits.TypedKernelWords
noncomputable section
open OAI.ExactFourier

abbrev C2 : Mat2 := C
abbrev Step := WordStep C2 2

theorem diagonal_isMonomial (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    IsMonomial (diagonal x y) := by
  refine ⟨Equiv.refl _, fun i => if i = 0 then x else y, ?_, ?_⟩
  · intro j
    fin_cases j
    · simpa using hx
    · simpa using hy
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [diagonal]

def diagonalStep (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) : Step :=
  .monomial (diagonal x y) (diagonal_isMonomial x y hx hy)

def forwardCall : Step := .call (Function.Embedding.refl (Fin 2))

theorem embeddedCall_refl {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) :
    embeddedCall A (Function.Embedding.refl (Fin q)) = A := by
  classical
  ext i j
  simp [embeddedCall]

@[simp] theorem forwardCall_matrix : forwardCall.matrix = C2 := embeddedCall_refl C2

@[simp] theorem diagonalStep_matrix (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    (diagonalStep x y hx hy).matrix = diagonal x y := rfl

theorem wordMatrix_append {q w : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (W V : List (WordStep A w)) : wordMatrix (W ++ V) = wordMatrix V * wordMatrix W := by
  simp [wordMatrix, List.reverse_append, List.prod_append]

theorem wordCalls_append {q w : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (W V : List (WordStep A w)) : wordCalls (W ++ V) = wordCalls W + wordCalls V := by
  simp [wordCalls]

@[simp] theorem wordMatrix_singleton {q w : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (s : WordStep A w) : wordMatrix [s] = s.matrix := by simp [wordMatrix]

@[simp] theorem wordMatrix_pair {q w : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (s r : WordStep A w) : wordMatrix [s, r] = r.matrix * s.matrix := by simp [wordMatrix]

def hadamardWord : List Step :=
  [diagonalStep 1 Complex.I one_ne_zero Complex.I_ne_zero,
   forwardCall,
   diagonalStep a⁻¹ (Complex.I * a⁻¹) (inv_ne_zero a_ne_zero)
     (mul_ne_zero Complex.I_ne_zero (inv_ne_zero a_ne_zero))]

theorem hadamardWord_matrix : wordMatrix hadamardWord = H := by
  have hd : diagonal a⁻¹ (Complex.I * a⁻¹) = a⁻¹ • S := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonal, S, smul_eq_mul, mul_comm]
  calc
    wordMatrix hadamardWord = diagonal a⁻¹ (Complex.I * a⁻¹) * C * S := by
      simp [wordMatrix, hadamardWord, forwardCall, diagonalStep, WordStep.matrix,
        embeddedCall_refl, S, Matrix.mul_assoc]
    _ = Hprime := by rw [hd]; simp [Hprime]
    _ = H := Hprime_eq_H

theorem hadamardWord_calls : wordCalls hadamardWord = 1 := by
  simp [wordCalls, hadamardWord, diagonalStep, forwardCall, WordStep.calls]

def shearWord (t : ℂ) (ht : t ≠ 0) : List Step :=
  [diagonalStep (5 / (4 * t)) 1 (div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) ht)) one_ne_zero] ++
  hadamardWord ++ [diagonalStep (-3) 1 (by norm_num) one_ne_zero] ++
  hadamardWord ++ [diagonalStep 2 1 (by norm_num) one_ne_zero] ++ hadamardWord ++
  [diagonalStep (-1 / 8) (-1 / 6) (by norm_num) (by norm_num),
   diagonalStep (4 * t / 5) 1 (div_ne_zero (mul_ne_zero (by norm_num) ht) (by norm_num)) one_ne_zero]

theorem shearWord_matrix (t : ℂ) (ht : t ≠ 0) : wordMatrix (shearWord t ht) = upperShear t := by
  calc
    wordMatrix (shearWord t ht) = D t * diagonal (-1 / 8) (-1 / 6) * K * diagonal (5 / (4 * t)) 1 := by
      simp only [shearWord, wordMatrix_append, wordMatrix_singleton, wordMatrix_pair,
        diagonalStep_matrix, hadamardWord_matrix]
      simp [D, K, Matrix.mul_assoc]
    _ = upperShear t := by
      rw [← D_inverse t ht]
      exact (upper_shear_formula t ht).symm

theorem shearWord_calls (t : ℂ) (ht : t ≠ 0) : wordCalls (shearWord t ht) = 3 := by
  simp [shearWord, wordCalls, hadamardWord, diagonalStep, forwardCall, WordStep.calls]

theorem compile_nonzero_shear (t : ℂ) (ht : t ≠ 0) :
    ∃ W : List (WordStep C2 2), wordMatrix W = upperShear t ∧ wordCalls W = 3 :=
  ⟨shearWord t ht, shearWord_matrix t ht, shearWord_calls t ht⟩

theorem swap_isMonomial : IsMonomial swap := by
  refine ⟨Equiv.swap 0 1, fun _ => 1, fun _ => one_ne_zero, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [swap, Equiv.swap_apply_def]

def inverseWord : List Step := [forwardCall, .monomial swap swap_isMonomial]

theorem inverseWord_matrix : wordMatrix inverseWord = C2⁻¹ := by
  simp only [inverseWord, wordMatrix_pair]
  rw [forwardCall_matrix]
  exact C_inverse.symm

theorem inverseWord_calls : wordCalls inverseWord = 1 := by
  simp [inverseWord, wordCalls, forwardCall, WordStep.calls]

theorem compile_inverse :
    ∃ W : List (WordStep C2 2), wordMatrix W = C2⁻¹ ∧ wordCalls W = 1 :=
  ⟨inverseWord, inverseWord_matrix, inverseWord_calls⟩

/-- Relabel both matrix indices and the ordered coordinates of every call. -/
theorem isMonomial_reindex {w v : ℕ} (e : Fin w ≃ Fin v)
    {M : Matrix (Fin w) (Fin w) ℂ} (hM : IsMonomial M) :
    IsMonomial (Matrix.reindex e e M) := by
  classical
  obtain ⟨σ, d, hd, h⟩ := hM
  refine ⟨e.symm.trans (σ.trans e), fun j => d (e.symm j), fun j => hd _, ?_⟩
  intro i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, h, Equiv.trans_apply]
  have he : e.symm i = σ (e.symm j) ↔ i = e (σ (e.symm j)) := e.symm_apply_eq
  simp only [he]
  rfl

theorem embeddedCall_reindex {q w v : ℕ} (A : Matrix (Fin q) (Fin q) ℂ)
    (f : Fin q ↪ Fin w) (e : Fin w ≃ Fin v) :
    embeddedCall A (f.trans e.toEmbedding) = Matrix.reindex e e (embeddedCall A f) := by
  classical
  ext i j
  simp [embeddedCall, Matrix.reindex_apply, ← e.eq_symm_apply]

def relabelStep {q w v : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (e : Fin w ≃ Fin v) : WordStep A w → WordStep A v
  | .monomial M hM => .monomial (Matrix.reindex e e M) (isMonomial_reindex e hM)
  | .call f => .call (f.trans e.toEmbedding)

@[simp] theorem relabelStep_matrix {q w v : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (e : Fin w ≃ Fin v) (s : WordStep A w) :
    (relabelStep e s).matrix = Matrix.reindex e e s.matrix := by
  cases s with
  | monomial M hM => rfl
  | call f => exact embeddedCall_reindex A f e

@[simp] theorem relabelStep_calls {q w v : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (e : Fin w ≃ Fin v) (s : WordStep A w) : (relabelStep e s).calls = s.calls := by
  cases s <;> rfl

def relabelWord {q w v : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (e : Fin w ≃ Fin v) (W : List (WordStep A w)) : List (WordStep A v) :=
  W.map (relabelStep e)

theorem relabelWord_matrix {q w v : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (e : Fin w ≃ Fin v) (W : List (WordStep A w)) :
    wordMatrix (relabelWord e W) = Matrix.reindex e e (wordMatrix W) := by
  simp only [relabelWord, wordMatrix, List.map_map, Function.comp_def, relabelStep_matrix]
  rw [show W.map (fun s => Matrix.reindex e e s.matrix) =
      (W.map WordStep.matrix).map (Matrix.reindexAlgEquiv ℂ ℂ e).toMonoidHom
      from (List.map_map ..).symm]
  rw [← List.map_reverse, ← map_list_prod]
  rfl

theorem relabelWord_calls {q w v : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (e : Fin w ≃ Fin v) (W : List (WordStep A w)) :
    wordCalls (relabelWord e W) = wordCalls W := by
  simp [relabelWord, wordCalls, List.map_map, Function.comp_def]

end
end ExactFourierCircuits.TypedKernelWords

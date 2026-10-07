import TypedKernelWords
import DirectionalWords
import OAI.Computability.FourierCircuit.PiTensor

namespace ExactFourierCircuits.TensorWords
noncomputable section
open OAI.ExactFourier
open scoped BigOperators

def embedStep {q w v : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (e : Fin w ↪ Fin v) : WordStep A w → WordStep A v
  | .monomial M hM => .monomial (Embedded.matrix e M)
      ((show MonomialMatrix M from hM).embed e)
  | .call f => .call (f.trans e)

@[simp] theorem embedStep_matrix {q w v : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (e : Fin w ↪ Fin v) (s : WordStep A w) :
    (embedStep e s).matrix = Embedded.matrix e s.matrix := by
  cases s with
  | monomial M hM => rfl
  | call f =>
    simp only [embedStep, WordStep.matrix, Packing.embeddedCall_eq]
    exact (Embedded.matrix_comp f e A).symm

@[simp] theorem embedStep_calls {q w v : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (e : Fin w ↪ Fin v) (s : WordStep A w) : (embedStep e s).calls = s.calls := by
  cases s <;> rfl

def embeddedWord {q w v : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (e : Fin w ↪ Fin v) (W : List (WordStep A w)) : List (WordStep A v) :=
  W.map (embedStep e)

theorem wordMatrix_cons {q w : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (s : WordStep A w) (W : List (WordStep A w)) :
    wordMatrix (s :: W) = wordMatrix W * s.matrix := by
  simp [wordMatrix]

theorem embeddedWord_matrix {q w v : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (e : Fin w ↪ Fin v) (W : List (WordStep A w)) :
    wordMatrix (embeddedWord e W) = Embedded.matrix e (wordMatrix W) := by
  induction W with
  | nil => simp [embeddedWord, wordMatrix]
  | cons s W ih =>
    simp only [embeddedWord, List.map_cons, wordMatrix_cons, embedStep_matrix]
    rw [← embeddedWord, ih, ← Embedded.matrix_mul]

theorem embeddedWord_calls {q w v : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (e : Fin w ↪ Fin v) (W : List (WordStep A w)) :
    wordCalls (embeddedWord e W) = wordCalls W := by
  simp [embeddedWord, wordCalls, List.map_map, Function.comp_def]

/-- The literal width is v; every coordinate outside the embedding is fixed. -/
theorem embeddedWord_blocks {q w v : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (e : Fin w ↪ Fin v) (W : List (WordStep A w)) :
    wordMatrix (embeddedWord e W) =
      Matrix.reindex (Embedded.coordinates e) (Embedded.coordinates e)
        (Matrix.fromBlocks (wordMatrix W) 0 0
          (1 : Matrix (Embedded.complement e) (Embedded.complement e) ℂ)) :=
  embeddedWord_matrix e W

theorem embeddedWord_on {q w v : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (e : Fin w ↪ Fin v) (W : List (WordStep A w)) (i j : Fin w) :
    wordMatrix (embeddedWord e W) (e i) (e j) = wordMatrix W i j := by
  rw [embeddedWord_matrix, Embedded.matrix_on]

theorem embeddedWord_off {q w v : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (e : Fin w ↪ Fin v) (W : List (WordStep A w)) (i j : Fin v)
    (hi : i ∉ Set.range e) : wordMatrix (embeddedWord e W) i j = if i = j then 1 else 0 := by
  rw [embeddedWord_matrix, Embedded.matrix_off_row e _ i j hi]

theorem wordMatrix_flatten {q w : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (L : List (List (WordStep A w))) :
    wordMatrix L.flatten = (L.map wordMatrix).reverse.prod := by
  induction L with
  | nil => simp [wordMatrix]
  | cons W L ih =>
    simp only [List.flatten_cons, TypedKernelWords.wordMatrix_append, ih,
      List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil, mul_one]

theorem wordCalls_flatten {q w : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (L : List (List (WordStep A w))) : wordCalls L.flatten = (L.map wordCalls).sum := by
  induction L with
  | nil => rfl
  | cons W L ih => simp [List.flatten_cons, TypedKernelWords.wordCalls_append, ih]

def parallelWord {q w v r : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (e : (Σ _ : Fin r, Fin w) ≃ Fin v) (W : List (WordStep A w)) : List (WordStep A v) :=
  (Finset.univ.toList.map (fun i : Fin r =>
    embeddedWord ((Embedded.sigmaIn i).trans e.toEmbedding) W)).reverse.flatten

theorem parallelWord_matrix {q w v r : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (e : (Σ _ : Fin r, Fin w) ≃ Fin v) (W : List (WordStep A w)) :
    wordMatrix (parallelWord e W) =
      Matrix.reindex e e (Matrix.blockDiagonal' (fun _ : Fin r => wordMatrix W)) := by
  simp only [parallelWord, wordMatrix_flatten, List.map_reverse, List.reverse_reverse,
    List.map_map, Function.comp_def, embeddedWord_matrix]
  simp_rw [← Embedded.matrix_comp, Embedded.matrix_equiv]
  rw [show Finset.univ.toList.map (fun i : Fin r =>
      Matrix.reindex e e (Embedded.matrix (Embedded.sigmaIn i) (wordMatrix W))) =
      (Finset.univ.toList.map (fun i : Fin r => Embedded.matrix (Embedded.sigmaIn i) (wordMatrix W))).map
        (Matrix.reindexAlgEquiv ℂ ℂ e).toMonoidHom from (List.map_map ..).symm]
  rw [← map_list_prod, Embedded.blockDiagonal'_product]
  rfl

theorem parallelWord_calls {q w v r : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (e : (Σ _ : Fin r, Fin w) ≃ Fin v) (W : List (WordStep A w)) :
    wordCalls (parallelWord e W) = r * wordCalls W := by
  simp [parallelWord, wordCalls_flatten, List.map_reverse, List.map_map, Function.comp_def,
    embeddedWord_calls]

abbrev bitEquiv : Fin 2 ≃ ZMod 2 := (ZMod.finEquiv 2).toEquiv

def binaryC : Matrix (ZMod 2) (ZMod 2) ℂ := Matrix.reindex bitEquiv bitEquiv C

theorem binaryC_apply (x y : ZMod 2) : binaryC x y = if x = y then a else b := by
  fin_cases x <;> fin_cases y <;> rfl

lemma binary_flip_eq (x y : ZMod 2) : x = y + 1 ↔ x ≠ y := by
  rcases DirectionalWords.binary_values x with rfl | rfl <;>
    rcases DirectionalWords.binary_values y with rfl | rfl <;>
    simp [CharTwo.add_self_eq_zero]

def tensorBits (n : ℕ) : (Fin n → Fin 2) ≃ DirectionalWords.Bits n :=
  Equiv.piCongrRight (fun _ : Fin n => bitEquiv)

/-- Carries the directional compiler's addresses to upstream tensorCoordinates. -/
def tensorRelabel (n : ℕ) : Fin (2 ^ n) ≃ Fin (2 ^ n) :=
  (DirectionalWords.addresses n).symm.trans
    ((tensorBits n).symm.trans (tensorCoordinates 2 n).symm)

theorem tensorCoordinates_bridge (n : ℕ) :
    Matrix.reindex (tensorRelabel n) (tensorRelabel n)
      (Matrix.reindex (DirectionalWords.addresses n) (DirectionalWords.addresses n)
        (PiTensor.matrix (fun _ : Fin n => binaryC))) = tensorPower C n := by
  ext i j
  simp [tensorRelabel, tensorBits, binaryC, bitEquiv, Matrix.reindex_apply,
    PiTensor.matrix, tensorPower]

abbrev unitDirection {n : ℕ} (p : Fin n) : DirectionalWords.Bits n := BinaryFrames.unit p

theorem unitDirection_pivot {n : ℕ} (p : Fin n) : unitDirection p p = 1 := by
  simp [BinaryFrames.unit]

theorem unit_axis_matrix {n : ℕ} (p : Fin n) :
    PiTensor.matrix (Function.update (1 : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ) p binaryC) =
      DirectionalWords.directionalMatrix (unitDirection p) := by
  classical
  rw [PiTensor.axis_matrix]
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, PiTensor.axisCoordinates_symm]
  by_cases hr : (fun i : {i // i ≠ p} => x i) = (fun i : {i // i ≠ p} => y i)
  · have heq : x = y ↔ x p = y p := by
      constructor
      · intro h; exact congrFun h p
      · intro h
        funext i
        by_cases hi : i = p
        · subst i; exact h
        · exact congrFun hr ⟨i, hi⟩
    have ht : x = y + unitDirection p ↔ x p = y p + 1 := by
      constructor
      · intro h
        simpa [BinaryFrames.unit] using congrFun h p
      · intro h
        funext i
        by_cases hi : i = p
        · subst i; simpa [BinaryFrames.unit] using h
        · simpa [BinaryFrames.unit, hi] using congrFun hr ⟨i, hi⟩
    by_cases h : x p = y p <;>
      simp [Matrix.blockDiagonal'_apply, hr, DirectionalWords.directionalMatrix,
        DirectionalWords.translation, permM, DirectionalWords.translationEquiv,
        Matrix.one_apply, heq, ht, binaryC_apply, binary_flip_eq, h]
  · have heq : x ≠ y := by
      intro h
      apply hr
      simp [h]
    have ht : x ≠ y + unitDirection p := by
      intro h
      apply hr
      funext i
      simpa [BinaryFrames.unit, i.property] using congrFun h i
    simp [Matrix.blockDiagonal'_apply, hr, DirectionalWords.directionalMatrix,
      DirectionalWords.translation, permM, DirectionalWords.translationEquiv,
      heq, ht]

theorem unit_axes_product (n : ℕ) :
    (Finset.univ.toList.map (fun p : Fin n =>
      DirectionalWords.directionalMatrix (unitDirection p))).prod =
      PiTensor.matrix (fun _ : Fin n => binaryC) := by
  simp_rw [← unit_axis_matrix]
  let upd := fun p : Fin n =>
    Function.update (1 : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ) p binaryC
  change (Finset.univ.toList.map (fun p : Fin n => PiTensor.hom (upd p))).prod = _
  rw [show Finset.univ.toList.map (fun p : Fin n => PiTensor.hom (upd p)) =
      (Finset.univ.toList.map upd).map PiTensor.hom from (List.map_map ..).symm]
  rw [← map_list_prod]
  change PiTensor.matrix ((Finset.univ.toList.map upd).prod) =
    PiTensor.matrix (fun _ : Fin n => binaryC)
  congr 1
  funext p
  rw [Embedded.list_update_prod _ _ (Finset.nodup_toList _)]
  simp

def unitAxisWord {n : ℕ} (p : Fin n) : List (WordStep C (2 ^ n)) :=
  DirectionalWords.directionalWordAt (unitDirection p) p (unitDirection_pivot p)

theorem unitAxisWord_matrix {n : ℕ} (p : Fin n) :
    wordMatrix (unitAxisWord p) = DirectionalWords.directionalC (unitDirection p) :=
  DirectionalWords.directionalWordAt_matrix _ _ _

theorem unitAxisWord_calls {n : ℕ} (hn : 1 ≤ n) (p : Fin n) :
    wordCalls (unitAxisWord p) = 2 ^ (n - 1) :=
  DirectionalWords.directionalWordAt_calls hn _ _ _

def unitAxesWord (n : ℕ) : List (WordStep C (2 ^ n)) :=
  (Finset.univ.toList.map (fun p : Fin n => unitAxisWord p)).reverse.flatten

theorem unitAxesWord_matrix (n : ℕ) :
    wordMatrix (unitAxesWord n) =
      Matrix.reindex (DirectionalWords.addresses n) (DirectionalWords.addresses n)
        (PiTensor.matrix (fun _ : Fin n => binaryC)) := by
  simp only [unitAxesWord, wordMatrix_flatten, List.map_reverse, List.reverse_reverse,
    List.map_map, Function.comp_def, unitAxisWord_matrix, DirectionalWords.directionalC]
  rw [show Finset.univ.toList.map (fun p : Fin n =>
      Matrix.reindex (DirectionalWords.addresses n) (DirectionalWords.addresses n)
        (DirectionalWords.directionalMatrix (unitDirection p))) =
      (Finset.univ.toList.map (fun p : Fin n => DirectionalWords.directionalMatrix (unitDirection p))).map
        (Matrix.reindexAlgEquiv ℂ ℂ (DirectionalWords.addresses n)).toMonoidHom
      from (List.map_map ..).symm]
  rw [← map_list_prod, unit_axes_product]
  rfl

theorem unitAxesWord_calls (n : ℕ) (hn : 1 ≤ n) :
    wordCalls (unitAxesWord n) = n * 2 ^ (n - 1) := by
  simp [unitAxesWord, wordCalls_flatten, List.map_reverse, List.map_map, Function.comp_def,
    unitAxisWord_calls hn]

def ordinaryTensorWord (n : ℕ) : List (WordStep C (2 ^ n)) :=
  TypedKernelWords.relabelWord (tensorRelabel n) (unitAxesWord n)

theorem ordinaryTensorWord_matrix (n : ℕ) :
    wordMatrix (ordinaryTensorWord n) = tensorPower C n := by
  rw [ordinaryTensorWord, TypedKernelWords.relabelWord_matrix, unitAxesWord_matrix,
    tensorCoordinates_bridge]

theorem ordinaryTensorWord_calls (n : ℕ) (hn : 1 ≤ n) :
    wordCalls (ordinaryTensorWord n) = n * 2 ^ (n - 1) := by
  rw [ordinaryTensorWord, TypedKernelWords.relabelWord_calls, unitAxesWord_calls n hn]

theorem compile_ordinary_tensor (n : ℕ) (hn : 1 ≤ n) :
    ∃ W : List (WordStep C (2 ^ n)),
      wordMatrix W = tensorPower C n ∧ wordCalls W = n * 2 ^ (n - 1) :=
  ⟨ordinaryTensorWord n, ordinaryTensorWord_matrix n, ordinaryTensorWord_calls n hn⟩

end
end ExactFourierCircuits.TensorWords

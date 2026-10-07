import TensorFusion
import RoleWords
import OAI.Computability.FourierCircuit.FiniteSeparation

set_option autoImplicit false
namespace ExactFourierCircuits.PaddingWords
open OAI.ExactFourier
open scoped BigOperators Kronecker
noncomputable section

lemma reindex_mul {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (M N : Matrix ι ι ℂ) :
    Matrix.reindex e e (M * N) = Matrix.reindex e e M * Matrix.reindex e e N :=
  (Matrix.reindexAlgEquiv ℂ ℂ e).map_mul M N

/-- A matrix acting identically on the address register of each role. -/
def copiesMatrix (w n : ℕ) (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    Matrix (Fin (w * 2 ^ n)) (Fin (w * 2 ^ n)) ℂ :=
  Matrix.reindex (RoleWords.roleAddresses w n) (RoleWords.roleAddresses w n)
    ((1 : Matrix (Fin w) (Fin w) ℂ) ⊗ₖ M)

def addressCopies (w n : ℕ) : (Σ _ : Fin w, Fin (2 ^ n)) ≃ Fin (w * 2 ^ n) :=
  (Equiv.sigmaEquivProd (Fin w) (Fin (2 ^ n))).trans (RoleWords.roleAddresses w n)

def ordinaryCopiesWord (w n : ℕ) : List (WordStep C (w * 2 ^ n)) :=
  TensorWords.parallelWord (addressCopies w n) (TensorWords.ordinaryTensorWord n)

lemma ordinaryTensorWord_calls_all (n : ℕ) :
    wordCalls (TensorWords.ordinaryTensorWord n) = n * 2 ^ (n - 1) := by
  cases n with
  | zero =>
    rw [TensorWords.ordinaryTensorWord, TypedKernelWords.relabelWord_calls]
    simp [TensorWords.unitAxesWord, wordCalls]
  | succ n => exact TensorWords.ordinaryTensorWord_calls _ (by omega)

lemma ordinaryCopiesWord_matrix (w n : ℕ) :
    wordMatrix (ordinaryCopiesWord w n) = copiesMatrix w n (tensorPower C n) := by
  rw [ordinaryCopiesWord, TensorWords.parallelWord_matrix, TensorWords.ordinaryTensorWord_matrix]
  ext i j
  obtain ⟨⟨i, a⟩, rfl⟩ := (RoleWords.roleAddresses w n).surjective i
  obtain ⟨⟨j, b⟩, rfl⟩ := (RoleWords.roleAddresses w n).surjective j
  simp [copiesMatrix, addressCopies, Matrix.reindex_apply, Matrix.blockDiagonal'_apply,
    Matrix.one_apply]

lemma ordinaryCopiesWord_calls (w n : ℕ) :
    wordCalls (ordinaryCopiesWord w n) = w * n * 2 ^ (n - 1) := by
  rw [ordinaryCopiesWord, TensorWords.parallelWord_calls, ordinaryTensorWord_calls_all]
  exact (Nat.mul_assoc _ _ _).symm

/-- Regroups active and padding address blocks using a prescribed role equivalence. -/
def blockCoordinates {w p v : ℕ} (n : ℕ) (e : Fin w ⊕ Fin p ≃ Fin v) :
    (Fin (w * 2 ^ n) ⊕ Fin (p * 2 ^ n)) ≃ Fin (v * 2 ^ n) :=
  (Equiv.sumCongr (RoleWords.roleAddresses w n).symm (RoleWords.roleAddresses p n).symm).trans
    ((Equiv.sumProdDistrib (Fin w) (Fin p) (Fin (2 ^ n))).symm.trans
      ((e.prodCongr (Equiv.refl _)).trans (RoleWords.roleAddresses v n)))

/-- Literal concatenation of two words on disjoint blocks; no coordinates are initialized. -/
def sumWord {w p v : ℕ} (e : Fin w ⊕ Fin p ≃ Fin v)
    (W : List (WordStep C w)) (V : List (WordStep C p)) : List (WordStep C v) :=
  TensorWords.embeddedWord (Function.Embedding.inl.trans e.toEmbedding) W ++
    TensorWords.embeddedWord (Function.Embedding.inr.trans e.toEmbedding) V

lemma sumWord_matrix {w p v : ℕ} (e : Fin w ⊕ Fin p ≃ Fin v)
    (W : List (WordStep C w)) (V : List (WordStep C p)) :
    wordMatrix (sumWord e W V) =
      Matrix.reindex e e (Matrix.fromBlocks (wordMatrix W) 0 0 (wordMatrix V)) := by
  rw [sumWord, TypedKernelWords.wordMatrix_append, TensorWords.embeddedWord_matrix,
    TensorWords.embeddedWord_matrix, ← Embedded.matrix_comp, ← Embedded.matrix_comp,
    Embedded.matrix_equiv, Embedded.matrix_equiv, ← reindex_mul,
    Embedded.matrix_inl, Embedded.matrix_inr]
  congr 1
  simp [Matrix.fromBlocks_multiply]

lemma sumWord_calls {w p v : ℕ} (e : Fin w ⊕ Fin p ≃ Fin v)
    (W : List (WordStep C w)) (V : List (WordStep C p)) :
    wordCalls (sumWord e W V) = wordCalls W + wordCalls V := by
  rw [sumWord, TypedKernelWords.wordCalls_append, TensorWords.embeddedWord_calls,
    TensorWords.embeddedWord_calls]

lemma copiesMatrix_blocks {w p v : ℕ} (n : ℕ) (e : Fin w ⊕ Fin p ≃ Fin v)
    (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    Matrix.reindex (blockCoordinates n e) (blockCoordinates n e)
      (Matrix.fromBlocks (copiesMatrix w n M) 0 0 (copiesMatrix p n M)) = copiesMatrix v n M := by
  ext i j
  obtain ⟨⟨i, a⟩, rfl⟩ := (RoleWords.roleAddresses v n).surjective i
  obtain ⟨⟨j, b⟩, rfl⟩ := (RoleWords.roleAddresses v n).surjective j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  cases i <;> cases j <;>
    simp [blockCoordinates, copiesMatrix, Matrix.reindex_apply, Matrix.one_apply,
      e.injective.eq_iff]

/-- Fill all extra roles by ordinary tensor words. -/
def fillWord {w p v : ℕ} (n : ℕ) (e : Fin w ⊕ Fin p ≃ Fin v)
    (W : List (WordStep C (w * 2 ^ n))) : List (WordStep C (v * 2 ^ n)) :=
  sumWord (blockCoordinates n e) W (ordinaryCopiesWord p n)

lemma fillWord_matrix {w p v : ℕ} (n : ℕ) (e : Fin w ⊕ Fin p ≃ Fin v)
    (W : List (WordStep C (w * 2 ^ n)))
    (hW : wordMatrix W = copiesMatrix w n (tensorPower C n)) :
    wordMatrix (fillWord n e W) = copiesMatrix v n (tensorPower C n) := by
  rw [fillWord, sumWord_matrix, hW, ordinaryCopiesWord_matrix, copiesMatrix_blocks]

lemma fillWord_calls {w p v : ℕ} (n : ℕ) (e : Fin w ⊕ Fin p ≃ Fin v)
    (W : List (WordStep C (w * 2 ^ n))) :
    wordCalls (fillWord n e W) = wordCalls W + p * n * 2 ^ (n - 1) := by
  rw [fillWord, sumWord_calls, ordinaryCopiesWord_calls]

def paddingRoles (w r : ℕ) (hw : w ≤ 2 ^ r) : Fin w ⊕ Fin (2 ^ r - w) ≃ Fin (2 ^ r) :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hw))

/-- First fill addresses, then execute the role-axis tensor word pointwise. -/
def paddedWord (w r n : ℕ) (hw : w ≤ 2 ^ r) (W : List (WordStep C (w * 2 ^ n))) :
    List (WordStep C (2 ^ r * 2 ^ n)) :=
  fillWord n (paddingRoles w r hw) W ++
    RoleWords.pointwiseWord n (TensorWords.ordinaryTensorWord r)

lemma paddedWord_matrix (w r n : ℕ) (hw : w ≤ 2 ^ r)
    (W : List (WordStep C (w * 2 ^ n)))
    (hW : wordMatrix W = copiesMatrix w n (tensorPower C n)) :
    wordMatrix (paddedWord w r n hw W) =
      Matrix.reindex (RoleWords.roleAddresses (2 ^ r) n) (RoleWords.roleAddresses (2 ^ r) n)
        (tensorPower C r ⊗ₖ tensorPower C n) := by
  rw [paddedWord, TypedKernelWords.wordMatrix_append, fillWord_matrix _ _ _ hW,
    RoleWords.pointwiseWord_matrix, TensorWords.ordinaryTensorWord_matrix]
  change Matrix.reindex _ _ (tensorPower C r ⊗ₖ 1) *
    Matrix.reindex _ _ (1 ⊗ₖ tensorPower C n) = _
  rw [← reindex_mul, ← Matrix.mul_kronecker_mul]
  simp

lemma role_axis_calls (r n : ℕ) (hn : 1 ≤ n) :
    2 ^ n * (r * 2 ^ (r - 1)) = r * 2 ^ r * 2 ^ (n - 1) := by
  cases n with
  | zero => omega
  | succ n =>
    cases r with
    | zero => simp
    | succ r => simp [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

lemma paddedWord_calls (w r n : ℕ) (hw : w ≤ 2 ^ r) (hn : 1 ≤ n)
    (W : List (WordStep C (w * 2 ^ n))) :
    wordCalls (paddedWord w r n hw W) = wordCalls W +
      (2 ^ r - w) * n * 2 ^ (n - 1) + r * 2 ^ r * 2 ^ (n - 1) := by
  rw [paddedWord, TypedKernelWords.wordCalls_append, fillWord_calls,
    RoleWords.pointwiseWord_calls, ordinaryTensorWord_calls_all, role_axis_calls _ _ hn]

def fusedCoordinates (r n : ℕ) : Fin (2 ^ r * 2 ^ n) ≃ Fin (2 ^ (r + n)) :=
  (RoleWords.roleAddresses (2 ^ r) n).symm.trans (TensorFusion.fusion r n)

/-- A literal word on exactly the fused tensor-power width. -/
def fusedWord (w r n : ℕ) (hw : w ≤ 2 ^ r) (W : List (WordStep C (w * 2 ^ n))) :
    List (WordStep C (2 ^ (r + n))) :=
  TypedKernelWords.relabelWord (fusedCoordinates r n) (paddedWord w r n hw W)

lemma fusedWord_matrix (w r n : ℕ) (hw : w ≤ 2 ^ r)
    (W : List (WordStep C (w * 2 ^ n)))
    (hW : wordMatrix W = copiesMatrix w n (tensorPower C n)) :
    wordMatrix (fusedWord w r n hw W) = tensorPower C (r + n) := by
  rw [fusedWord, TypedKernelWords.relabelWord_matrix, paddedWord_matrix _ _ _ _ _ hW,
    reindex_comp]
  have h : (RoleWords.roleAddresses (2 ^ r) n).trans (fusedCoordinates r n) =
      TensorFusion.fusion r n := by ext x; simp [fusedCoordinates]
  rw [h, TensorFusion.fusion_tensor]

lemma fusedWord_calls (w r n : ℕ) (hw : w ≤ 2 ^ r) (hn : 1 ≤ n)
    (W : List (WordStep C (w * 2 ^ n))) :
    wordCalls (fusedWord w r n hw W) = wordCalls W +
      (2 ^ r - w) * n * 2 ^ (n - 1) + r * 2 ^ r * 2 ^ (n - 1) := by
  rw [fusedWord, TypedKernelWords.relabelWord_calls, paddedWord_calls _ _ _ _ hn]

/-- Apply the directional-to-upstream address relabel independently in every active role. -/
def addressRelabel (w n : ℕ) : Fin (w * 2 ^ n) ≃ Fin (w * 2 ^ n) :=
  (RoleWords.roleAddresses w n).symm.trans
    (((Equiv.refl (Fin w)).prodCongr (TensorWords.tensorRelabel n)).trans
      (RoleWords.roleAddresses w n))

lemma copiesMatrix_addressRelabel (w n : ℕ) (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    Matrix.reindex (addressRelabel w n) (addressRelabel w n) (copiesMatrix w n M) =
      copiesMatrix w n (Matrix.reindex (TensorWords.tensorRelabel n) (TensorWords.tensorRelabel n) M) := by
  ext i j
  obtain ⟨⟨i, a⟩, rfl⟩ := (RoleWords.roleAddresses w n).surjective i
  obtain ⟨⟨j, b⟩, rfl⟩ := (RoleWords.roleAddresses w n).surjective j
  simp [copiesMatrix, addressRelabel, Matrix.reindex_apply, Matrix.one_apply]

def canonicalNetworkWord (w n : ℕ) (W : List (WordStep C (w * 2 ^ n))) :
    List (WordStep C (w * 2 ^ n)) :=
  TypedKernelWords.relabelWord (addressRelabel w n) W

lemma canonicalNetworkWord_matrix (w n : ℕ) (W : List (WordStep C (w * 2 ^ n)))
    (hW : wordMatrix W = copiesMatrix w n (wordMatrix (TensorWords.unitAxesWord n))) :
    wordMatrix (canonicalNetworkWord w n W) = copiesMatrix w n (tensorPower C n) := by
  rw [canonicalNetworkWord, TypedKernelWords.relabelWord_matrix, hW, copiesMatrix_addressRelabel]
  congr 1
  rw [← TensorWords.ordinaryTensorWord_matrix n]
  exact (TypedKernelWords.relabelWord_matrix _ _).symm

lemma canonicalNetworkWord_calls (w n : ℕ) (W : List (WordStep C (w * 2 ^ n))) :
    wordCalls (canonicalNetworkWord w n W) = wordCalls W :=
  TypedKernelWords.relabelWord_calls _ _

/-- Canonicalize, pad, execute the role tensor, then fuse to the upstream tensor coordinates. -/
def extendedWord (w r n : ℕ) (hw : w ≤ 2 ^ r) (W : List (WordStep C (w * 2 ^ n))) :
    List (WordStep C (2 ^ (r + n))) :=
  fusedWord w r n hw (canonicalNetworkWord w n W)

lemma extendedWord_matrix (w r n : ℕ) (hw : w ≤ 2 ^ r)
    (W : List (WordStep C (w * 2 ^ n)))
    (hW : wordMatrix W = copiesMatrix w n (wordMatrix (TensorWords.unitAxesWord n))) :
    wordMatrix (extendedWord w r n hw W) = tensorPower C (r + n) :=
  fusedWord_matrix _ _ _ _ _ (canonicalNetworkWord_matrix _ _ _ hW)

lemma extendedWord_calls (w r n : ℕ) (hw : w ≤ 2 ^ r) (hn : 1 ≤ n)
    (W : List (WordStep C (w * 2 ^ n))) :
    wordCalls (extendedWord w r n hw W) = wordCalls W +
      (2 ^ r - w) * n * 2 ^ (n - 1) + r * 2 ^ r * 2 ^ (n - 1) := by
  rw [extendedWord, fusedWord_calls _ _ _ _ hn, canonicalNetworkWord_calls]

/-- Padding exactly preserves the saving measured against the ordinary tensor cost. -/
lemma ordinary_cost_balance (w r n : ℕ) (hw : w ≤ 2 ^ r) (hn : 1 ≤ n) :
    w * n * 2 ^ (n - 1) + (2 ^ r - w) * n * 2 ^ (n - 1) +
      r * 2 ^ r * 2 ^ (n - 1) = (r + n) * 2 ^ (r + n - 1) := by
  have hp : w + (2 ^ r - w) = 2 ^ r := Nat.add_sub_of_le hw
  have hpow : 2 ^ r * 2 ^ (n - 1) = 2 ^ (r + n - 1) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ = ((w + (2 ^ r - w)) * n + r * 2 ^ r) * 2 ^ (n - 1) := by ring
    _ = (r + n) * (2 ^ r * 2 ^ (n - 1)) := by rw [hp]; ring
    _ = _ := by rw [hpow]

lemma fusedWord_saving (w r n margin : ℕ) (hw : w ≤ 2 ^ r) (hn : 1 ≤ n)
    (W : List (WordStep C (w * 2 ^ n)))
    (hcost : wordCalls W + margin ≤ w * n * 2 ^ (n - 1)) :
    wordCalls (fusedWord w r n hw W) + margin ≤ (r + n) * 2 ^ (r + n - 1) := by
  rw [fusedWord_calls _ _ _ _ hn, ← ordinary_cost_balance _ _ _ hw hn]
  omega

theorem compile_padded_tensor (w r n : ℕ) (hw : w ≤ 2 ^ r) (hn : 1 ≤ n)
    (W : List (WordStep C (w * 2 ^ n)))
    (hW : wordMatrix W = copiesMatrix w n (tensorPower C n)) :
    ∃ V : List (WordStep C (2 ^ (r + n))), wordMatrix V = tensorPower C (r + n) ∧
      wordCalls V = wordCalls W + (2 ^ r - w) * n * 2 ^ (n - 1) + r * 2 ^ r * 2 ^ (n - 1) :=
  ⟨fusedWord w r n hw W, fusedWord_matrix _ _ _ _ _ hW, fusedWord_calls _ _ _ _ hn W⟩

/-- This generic extension consumes a proved network action and cost; it does not supply them. -/
theorem extend_network_saving (w r n margin : ℕ) (hw : w ≤ 2 ^ r) (hn : 1 ≤ n)
    (W : List (WordStep C (w * 2 ^ n)))
    (hW : wordMatrix W = copiesMatrix w n (wordMatrix (TensorWords.unitAxesWord n)))
    (hcost : wordCalls W + margin ≤ w * n * 2 ^ (n - 1)) :
    ∃ V : List (WordStep C (2 ^ (r + n))), wordMatrix V = tensorPower C (r + n) ∧
      wordCalls V + margin ≤ (r + n) * 2 ^ (r + n - 1) := by
  refine ⟨extendedWord w r n hw W, extendedWord_matrix _ _ _ _ _ hW, ?_⟩
  exact fusedWord_saving _ _ _ _ hw hn (canonicalNetworkWord w n W)
    (by simpa only [canonicalNetworkWord_calls] using hcost)

end
end ExactFourierCircuits.PaddingWords

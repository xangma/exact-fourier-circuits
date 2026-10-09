import UniformLayerSnapshot

set_option autoImplicit false

namespace ExactFourierCircuits.UniformLayerSnapshot
noncomputable section
open OAI.ExactFourier UniformLayerRestriction UniformLocalFourierLayers

def flattenEquiv {σ : Type} (I : σ → Type) :
    (Σ _ : (Σ i, I i), Fin 2) ≃ (Σ i, (Σ _ : I i, Fin 2)) where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv := by rintro ⟨⟨i,j⟩,x⟩; rfl
  right_inv := by rintro ⟨i,⟨j,x⟩⟩; rfl

theorem flatten_constant_blocks {σ : Type} [Fintype σ] [DecidableEq σ]
    (I : σ → Type) [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)] :
    Matrix.reindex (flattenEquiv I) (flattenEquiv I)
      (Matrix.blockDiagonal' (fun _ : (Σ i, I i) => C)) =
      Matrix.blockDiagonal' (fun i => Matrix.blockDiagonal' (fun _ : I i => C)) := by
  ext ⟨i,⟨a,x⟩⟩ ⟨j,⟨b,y⟩⟩
  by_cases hij : i = j
  · subst j
    by_cases hab : a = b
    · subst b; simp [Matrix.reindex_apply, flattenEquiv, Matrix.blockDiagonal'_apply]
    · simp [Matrix.reindex_apply, flattenEquiv, Matrix.blockDiagonal'_apply, hab]
  · simp [Matrix.reindex_apply, flattenEquiv, Matrix.blockDiagonal'_apply, hij]

namespace Calls
variable {σ : Type} [Fintype σ] [DecidableEq σ]

def blocks (P : σ → Calls (Fin 2)) : Calls (Σ _ : σ, Fin 2) where
  index := Σ i, (P i).index
  finite := inferInstance
  dec := inferInstance
  position := (flattenEquiv (fun i => (P i).index)).toEmbedding.trans
    (Embedded.sigmaEmbed (fun i => (P i).position))

@[simp] theorem blocks_matrix (P : σ → Calls (Fin 2)) :
    (blocks P).matrix = Matrix.blockDiagonal' (fun i => (P i).matrix) := by
  change Embedded.matrix
    ((flattenEquiv (fun i => (P i).index)).toEmbedding.trans
      (Embedded.sigmaEmbed (fun i => (P i).position)))
    (Matrix.blockDiagonal' (fun _ : (Σ i, (P i).index) => C)) = _
  rw [← Embedded.matrix_comp, Embedded.matrix_equiv, flatten_constant_blocks,
    Embedded.matrix_sigmaEmbed]
  rfl

end Calls

namespace Snapshot
variable {σ : Type} [Fintype σ] [DecidableEq σ]

def blocks (S : σ → Snapshot (Fin 2)) : Snapshot (Σ _ : σ, Fin 2) where
  calls := Calls.blocks (fun i => (S i).calls)
  diagonal x := (S x.1).diagonal x.2
  nonzero x := (S x.1).nonzero x.2
  active_one := by
    change ∀ x : (Σ _ : (Σ i, (S i).calls.index), Fin 2),
      (S x.1.1).diagonal ((S x.1.1).calls.position ⟨x.1.2, x.2⟩) = 1
    intro x
    exact (S x.1.1).active_one _

@[simp] theorem blocks_matrix (S : σ → Snapshot (Fin 2)) :
    (blocks S).matrix = Matrix.blockDiagonal' (fun i => (S i).matrix) := by
  have hd : Matrix.diagonal (fun x : (Σ _ : σ, Fin 2) => (S x.1).diagonal x.2) =
      Matrix.blockDiagonal' (fun i => Matrix.diagonal (S i).diagonal) := by
    ext ⟨i,x⟩ ⟨j,y⟩
    by_cases hij : i = j
    · subst j; simp [Matrix.diagonal_apply, Matrix.blockDiagonal'_apply]
    · simp [Matrix.blockDiagonal'_apply, hij]
  change Matrix.diagonal (fun x : (Σ _ : σ, Fin 2) => (S x.1).diagonal x.2) *
    (Calls.blocks (fun i => (S i).calls)).matrix = _
  rw [hd, Calls.blocks_matrix, ← Matrix.blockDiagonal'_mul]
  rfl

end Snapshot

/-- Disjointness is inherited from the layer constructors' embeddings. -/
theorem layer_snapshot {n : ℕ} (L : Layer n) (hL : Restricted L) :
    ∃ S : Snapshot (Fin n), L.matrix = S.matrix := by
  induction L with
  | step s => simpa only [Layer.step_matrix] using step_snapshot s hL
  | parallel e L R ihL ihR =>
    obtain ⟨S,hS⟩ := ihL hL.1
    obtain ⟨T,hT⟩ := ihR hL.2
    refine ⟨(S.sum T).reindex e, ?_⟩
    rw [Layer.parallel_matrix, hS, hT, Snapshot.reindex_matrix, Snapshot.sum_matrix]
  | embed e L ih =>
    obtain ⟨S,hS⟩ := ih hL
    exact ⟨S.embed e, by rw [Layer.embed_matrix, hS, Snapshot.embed_matrix]⟩
  | @batch s n position steps =>
    have h : ∀ i, ∃ S : Snapshot (Fin 2), (steps i).matrix = S.matrix :=
      fun i => step_snapshot (steps i) (hL i)
    choose S hS using h
    refine ⟨(Snapshot.blocks S).embed position, ?_⟩
    rw [Layer.batch_matrix, Snapshot.embed_matrix, Snapshot.blocks_matrix]
    congr 2
    funext i
    exact hS i

theorem constant_blocks_reindex {σ τ : Type} [Fintype σ] [Fintype τ]
    [DecidableEq σ] [DecidableEq τ] (e : σ ≃ τ) :
    Matrix.reindex (Equiv.sigmaCongrLeft e) (Equiv.sigmaCongrLeft e)
      (Matrix.blockDiagonal' (fun _ : σ => C)) = Matrix.blockDiagonal' (fun _ : τ => C) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  by_cases hij : i = j
  · subst j; simp [Matrix.reindex_apply, Equiv.sigmaCongrLeft, Matrix.blockDiagonal'_apply]
  · have h' : e.symm i ≠ e.symm j := e.symm.injective.ne hij
    simp [Matrix.reindex_apply, Equiv.sigmaCongrLeft, Matrix.blockDiagonal'_apply, hij, h']

/-- A finite presentation for the physical matching-table consumer. -/
theorem finite_snapshot {n : ℕ} (L : Layer n) (hL : Restricted L) :
    ∃ (s : ℕ) (d : Fin n → ℂ) (position : (Σ _ : Fin s, Fin 2) ↪ Fin n),
      (∀ i, d i ≠ 0) ∧ (∀ i, d (position i) = 1) ∧
      L.matrix = Matrix.diagonal d *
        Embedded.matrix position (Matrix.blockDiagonal' (fun _ : Fin s => C)) := by
  obtain ⟨S,hS⟩ := layer_snapshot L hL
  let e : (Σ _ : S.calls.index, Fin 2) ≃ (Σ _ : Fin (Fintype.card S.calls.index), Fin 2) :=
    Equiv.sigmaCongrLeft (β := fun _ : Fin (Fintype.card S.calls.index) => Fin 2)
      (Fintype.equivFin S.calls.index)
  let position := e.symm.toEmbedding.trans S.calls.position
  refine ⟨Fintype.card S.calls.index, S.diagonal, position, S.nonzero, ?_, ?_⟩
  · intro i
    exact S.active_one (e.symm i)
  · rw [hS]
    change Matrix.diagonal S.diagonal * S.calls.matrix = _
    congr 1
    have h := Embedded.matrix_domain e S.calls.position
      (Matrix.blockDiagonal' (fun _ : S.calls.index => C))
    rw [constant_blocks_reindex] at h
    exact h.symm

theorem render_finite_snapshot {n : ℕ} (P : UniformBalancedToeplitz.Plan n)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0)
    (L : Layer n) (hL : L ∈ render P f hf) :
    ∃ (s : ℕ) (d : Fin n → ℂ) (position : (Σ _ : Fin s, Fin 2) ↪ Fin n),
      (∀ i, d i ≠ 0) ∧ (∀ i, d (position i) = 1) ∧
      L.matrix = Matrix.diagonal d *
        Embedded.matrix position (Matrix.blockDiagonal' (fun _ : Fin s => C)) :=
  finite_snapshot L (render_restricted P f hf L hL)

end
end ExactFourierCircuits.UniformLayerSnapshot

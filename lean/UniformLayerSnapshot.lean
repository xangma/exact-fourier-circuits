import UniformLayerRestriction

set_option autoImplicit false

namespace ExactFourierCircuits.UniformLayerSnapshot
noncomputable section
open OAI.ExactFourier UniformLayerRestriction UniformLocalFourierLayers

/-- A finite family of ordered, pairwise disjoint kernel calls. -/
structure Calls (α : Type) [Fintype α] [DecidableEq α] where
  index : Type
  finite : Fintype index
  dec : DecidableEq index
  position : (Σ _ : index, Fin 2) ↪ α

attribute [instance] Calls.finite Calls.dec

namespace Calls
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def matrix (P : Calls α) : Matrix α α ℂ :=
  Embedded.matrix P.position (Matrix.blockDiagonal' (fun _ : P.index => C))

def empty : Calls α where
  index := Fin 0
  finite := inferInstance
  dec := inferInstance
  position := ⟨fun i => Fin.elim0 i.1, by intro i; exact Fin.elim0 i.1⟩

@[simp] theorem empty_matrix : (empty : Calls α).matrix = 1 := by
  have h : Matrix.blockDiagonal' (fun _ : (empty : Calls α).index => C) = 1 := by
    ext ⟨i, x⟩; exact Fin.elim0 i
  rw [matrix, h, Embedded.matrix_one]

def single (e : Fin 2 ↪ α) : Calls α where
  index := Fin 1
  finite := inferInstance
  dec := inferInstance
  position := ⟨fun i => e i.2, by
    rintro ⟨i, x⟩ ⟨j, y⟩ h
    have hxy : x = y := e.injective h
    subst y
    have hij : i = j := Subsingleton.elim _ _
    subst j
    rfl⟩

@[simp] theorem single_matrix (e : Fin 2 ↪ α) : (single e).matrix = Embedded.matrix e C := by
  let p : (Σ _ : Fin 1, Fin 2) ↪ Fin 2 :=
    ⟨fun i => i.2, by
      rintro ⟨i,x⟩ ⟨j,y⟩ h
      dsimp at h
      subst y
      have hij : i = j := Subsingleton.elim _ _
      subst j
      rfl⟩
  have h : Embedded.matrix p (Matrix.blockDiagonal' (fun _ : Fin 1 => C)) = C := by
    ext i j
    change Embedded.matrix p _ (p ⟨0,i⟩) (p ⟨0,j⟩) = _
    rw [Embedded.matrix_on]
    simp
  change Embedded.matrix (p.trans e) (Matrix.blockDiagonal' (fun _ : Fin 1 => C)) = _
  rw [← Embedded.matrix_comp, h]

def embed (P : Calls α) (e : α ↪ β) : Calls β :=
  { P with position := P.position.trans e }

@[simp] theorem embed_matrix (P : Calls α) (e : α ↪ β) :
    (P.embed e).matrix = Embedded.matrix e P.matrix :=
  (Embedded.matrix_comp P.position e _).symm

def sum (P : Calls α) (Q : Calls β) : Calls (α ⊕ β) where
  index := P.index ⊕ Q.index
  finite := inferInstance
  dec := inferInstance
  position := PairFamily.sumEquiv.toEmbedding.trans (P.position.sumMap Q.position)

@[simp] theorem sum_matrix (P : Calls α) (Q : Calls β) :
    (P.sum Q).matrix = Matrix.fromBlocks P.matrix 0 0 Q.matrix := by
  change Embedded.matrix (PairFamily.sumEquiv.toEmbedding.trans (P.position.sumMap Q.position))
    (Matrix.blockDiagonal' (fun _ : P.index ⊕ Q.index => C)) = _
  rw [← Embedded.matrix_comp, Embedded.matrix_equiv]
  have h : (fun _ : P.index ⊕ Q.index => C) =
      Sum.elim (fun _ : P.index => C) (fun _ : Q.index => C) := by
    funext i; cases i <;> rfl
  rw [h, PairFamily.sum_blocks, Embedded.matrix_sumMap]
  rfl

end Calls

/-- A layer factors into a nonsingular diagonal and its disjoint ordered calls.
The diagonal is identically one on every active call endpoint. -/
structure Snapshot (α : Type) [Fintype α] [DecidableEq α] where
  calls : Calls α
  diagonal : α → ℂ
  nonzero : ∀ i, diagonal i ≠ 0
  active_one : ∀ i, diagonal (calls.position i) = 1

namespace Snapshot
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def matrix (S : Snapshot α) : Matrix α α ℂ := Matrix.diagonal S.diagonal * S.calls.matrix

def ofDiagonal (d : α → ℂ) (hd : ∀ i, d i ≠ 0) : Snapshot α where
  calls := Calls.empty
  diagonal := d
  nonzero := hd
  active_one i := Fin.elim0 i.1

@[simp] theorem ofDiagonal_matrix (d : α → ℂ) (hd : ∀ i, d i ≠ 0) :
    (ofDiagonal d hd).matrix = Matrix.diagonal d := by
  simp [matrix, ofDiagonal]

def ofCall (e : Fin 2 ↪ α) : Snapshot α where
  calls := Calls.single e
  diagonal := fun _ => 1
  nonzero := fun _ => one_ne_zero
  active_one := fun _ => rfl

@[simp] theorem ofCall_matrix (e : Fin 2 ↪ α) :
    (ofCall e).matrix = Embedded.matrix e C := by
  simp [matrix, ofCall]

def embed (S : Snapshot α) (e : α ↪ β) : Snapshot β where
  calls := S.calls.embed e
  diagonal := fun i => Embedded.matrix e (Matrix.diagonal S.diagonal) i i
  nonzero := by
    have hu := Embedded.unit e (Matrix.diagonal S.diagonal)
      (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr (fun i => isUnit_iff_ne_zero.mpr (S.nonzero i))))
    rw [embedded_diagonal e S.diagonal] at hu
    intro i
    exact isUnit_iff_ne_zero.mp (Pi.isUnit_iff.mp (Matrix.isUnit_diagonal.mp hu) i)
  active_one := by
    change ∀ i : (Σ _ : S.calls.index, Fin 2),
      Embedded.matrix e (Matrix.diagonal S.diagonal) (e (S.calls.position i)) (e (S.calls.position i)) = 1
    intro i
    rw [Embedded.matrix_on, Matrix.diagonal_apply_eq]
    exact S.active_one i

@[simp] theorem embed_matrix (S : Snapshot α) (e : α ↪ β) :
    (S.embed e).matrix = Embedded.matrix e S.matrix := by
  change Matrix.diagonal (fun i => Embedded.matrix e (Matrix.diagonal S.diagonal) i i) *
    (S.calls.embed e).matrix = _
  rw [Calls.embed_matrix]
  rw [← embedded_diagonal, ← Embedded.matrix_mul]
  rfl

def sum (S : Snapshot α) (T : Snapshot β) : Snapshot (α ⊕ β) where
  calls := S.calls.sum T.calls
  diagonal := Sum.elim S.diagonal T.diagonal
  nonzero := by intro i; cases i with | inl i => exact S.nonzero i | inr i => exact T.nonzero i
  active_one := by
    rintro ⟨i, x⟩
    cases i with
    | inl i => exact S.active_one ⟨i, x⟩
    | inr i => exact T.active_one ⟨i, x⟩

@[simp] theorem sum_matrix (S : Snapshot α) (T : Snapshot β) :
    (S.sum T).matrix = Matrix.fromBlocks S.matrix 0 0 T.matrix := by
  have hd : Matrix.diagonal (Sum.elim S.diagonal T.diagonal) =
      Matrix.fromBlocks (Matrix.diagonal S.diagonal) 0 0 (Matrix.diagonal T.diagonal) := by
    ext i j; cases i <;> cases j <;> simp [Matrix.diagonal_apply, Matrix.fromBlocks]
  change Matrix.diagonal (Sum.elim S.diagonal T.diagonal) * (S.calls.sum T.calls).matrix = _
  rw [Calls.sum_matrix]
  rw [hd, Matrix.fromBlocks_multiply]
  simp [matrix]

def reindex (S : Snapshot α) (e : α ≃ β) : Snapshot β := S.embed e.toEmbedding

@[simp] theorem reindex_matrix (S : Snapshot α) (e : α ≃ β) :
    (S.reindex e).matrix = Matrix.reindex e e S.matrix := by
  rw [reindex, embed_matrix, Embedded.matrix_equiv]

end Snapshot

theorem monomial_diagonal_nonzero {n : ℕ} {d : Fin n → ℂ}
    (h : IsMonomial (Matrix.diagonal d)) : ∀ i, d i ≠ 0 := by
  have hu := MonomialMatrix.unit _ h
  intro i
  exact isUnit_iff_ne_zero.mp (Pi.isUnit_iff.mp (Matrix.isUnit_diagonal.mp hu) i)

theorem step_snapshot {n : ℕ} (s : WordStep C n) (hs : StepRestricted s) :
    ∃ S : Snapshot (Fin n), s.matrix = S.matrix := by
  cases s with
  | monomial M hM =>
    obtain ⟨d, rfl⟩ := hs
    exact ⟨Snapshot.ofDiagonal d (monomial_diagonal_nonzero hM), (Snapshot.ofDiagonal_matrix ..).symm⟩
  | call e =>
    exact ⟨Snapshot.ofCall e, by rw [Snapshot.ofCall_matrix]; exact Packing.embeddedCall_eq _ _⟩

end
end ExactFourierCircuits.UniformLayerSnapshot

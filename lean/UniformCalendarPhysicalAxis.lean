import UniformAllAxisFourierSnapshots
import UniformMatchingKernelAmbient

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarPhysicalAxis
noncomputable section
open OAI.ExactFourier UniformLayerSnapshot UniformSectorPacking
open UniformMatchingKernelAmbient UniformMatchingKernelGeometry

/-- A finite enumeration of the actual snapshot's entire ordered call union. -/
def position {r : ℕ} (S : Snapshot (Fin r)) :
    (Σ _ : Fin (Fintype.card S.calls.index),Fin 2) ↪ Fin r :=
  (Equiv.sigmaCongrLeft (β := fun _ : Fin (Fintype.card S.calls.index) => Fin 2)
    (Fintype.equivFin S.calls.index)).symm.toEmbedding.trans S.calls.position

theorem position_matrix {r : ℕ} (S : Snapshot (Fin r)) :
    Embedded.matrix (position S)
      (Matrix.blockDiagonal' (fun _ : Fin (Fintype.card S.calls.index) => C)) = S.calls.matrix := by
  have h := Embedded.matrix_domain
    (Equiv.sigmaCongrLeft (β := fun _ : Fin (Fintype.card S.calls.index) => Fin 2)
      (Fintype.equivFin S.calls.index)) S.calls.position
    (Matrix.blockDiagonal' (fun _ : S.calls.index => C))
  rw [constant_blocks_reindex] at h
  exact h

def geometry {r : ℕ} (S : Snapshot (Fin r)) (hp : 2≤r) : Axis :=
  UniformMatchingAxisTableMachine.geometry r (edges (position S))
    (matching (position S)) (range (position S)) hp

def coordinate {r : ℕ} (S : Snapshot (Fin r)) (hp : 2≤r) :
    Fin (geometry S hp).widths.sum ≃ Fin r :=
  UniformMatchingKernelAmbient.coordinate r (edges (position S))
    (matching (position S)) (range (position S)) hp

def diagonal {r : ℕ} (S : Snapshot (Fin r)) (hp : 2≤r) : Fin (geometry S hp).widths.sum→ℂ :=
  fun i => S.diagonal (coordinate S hp i)

theorem kernel {r : ℕ} (S : Snapshot (Fin r)) (hp : 2≤r) :
    Matrix.reindex (coordinate S hp) (coordinate S hp) (localKernel (geometry S hp))=S.calls.matrix := by
  unfold coordinate geometry
  rw [UniformMatchingKernelAmbient.union_kernel,position_matrix]

theorem diagonal_matrix {r : ℕ} (S : Snapshot (Fin r)) (hp : 2≤r) :
    Matrix.reindex (coordinate S hp) (coordinate S hp) (Matrix.diagonal (diagonal S hp)) =
      Matrix.diagonal S.diagonal := by
  ext i j
  by_cases eq : i=j
  · subst j
    simp [Matrix.reindex_apply,diagonal]
  · have ne : (coordinate S hp).symm i≠(coordinate S hp).symm j := (coordinate S hp).symm.injective.ne eq
    simp [Matrix.reindex_apply,eq,ne]

/-- The real55 axis geometry for this call union, followed by its actual
calendar diagonal, is exactly the complete calendar snapshot. -/
theorem factor {r : ℕ} (S : Snapshot (Fin r)) (hp : 2≤r) :
    Matrix.reindex (coordinate S hp) (coordinate S hp)
      (Matrix.diagonal (diagonal S hp) * localKernel (geometry S hp)) = S.matrix := by
  rw [←Embedded.matrix_equiv (coordinate S hp),Embedded.matrix_mul,
    Embedded.matrix_equiv,Embedded.matrix_equiv,diagonal_matrix,kernel]
  rfl

end
end ExactFourierCircuits.UniformCalendarPhysicalAxis

import UniformCalendarEventProducts

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarCallReindex
noncomputable section
open OAI.ExactFourier UniformLayerSnapshot UniformGlobalCalendarUnion TypedKernelWords

/-- Reordering independent calls preserves their embedded kernel, including a
separate permutation within each active event. -/
theorem calls_matrix {α ι : Type} [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι] (P : UniformLayerSnapshot.Calls α)
    (order : ι ≃ P.index) (position : (Σ _ : ι, Fin 2) ↪ α)
    (points : ∀ i side, position ⟨i,side⟩ = P.position ⟨order i,side⟩) :
    Embedded.matrix position (Matrix.blockDiagonal' (fun _ : ι => C)) =
      P.matrix := by
  let e : (Σ _ : P.index, Fin 2) ≃ (Σ _ : ι, Fin 2) :=
    Equiv.sigmaCongrLeft (β := fun _ : ι => Fin 2) order.symm
  have same : e.symm.toEmbedding.trans P.position = position := by
    ext ⟨i,side⟩
    simpa [e, Equiv.sigmaCongrLeft] using (points i side).symm
  have h := Embedded.matrix_domain e P.position
    (Matrix.blockDiagonal' (fun _ : P.index => C))
  rw [constant_blocks_reindex, same] at h
  exact h

/-- A caller's event order and local call order compose to the union's index. -/
def familyOrder {σ τ : Type} {I : σ → Type} {J : τ → Type}
    (events : σ ≃ τ) (calls : ∀ i, I i ≃ J (events i)) :
    (Σ i, I i) ≃ (Σ j, J j) :=
  (Equiv.sigmaCongrRight calls).trans (Equiv.sigmaCongrLeft events)

@[simp] lemma familyOrder_apply {σ τ : Type} {I : σ → Type} {J : τ → Type}
    (events : σ ≃ τ) (calls : ∀ i, I i ≃ J (events i)) (i : σ) (j : I i) :
    familyOrder events calls ⟨i,j⟩ = ⟨events i,calls i j⟩ := rfl

end
end ExactFourierCircuits.UniformCalendarCallReindex

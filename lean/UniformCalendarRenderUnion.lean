import UniformCalendarRenderAffine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarRenderUnion
noncomputable section
open OAI.ExactFourier
open scoped BigOperators

theorem blocks_perturbations {σ : Type} [Fintype σ] [DecidableEq σ]
    {β : σ → Type} [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (M : ∀ i, Matrix (β i) (β i) ℂ) :
    Matrix.blockDiagonal' M =
      1 + ∑ i, (Embedded.matrix (Embedded.sigmaIn i) (M i) - 1) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  simp only [Matrix.add_apply,Matrix.sum_apply,Matrix.sub_apply]
  have outside (k : σ) (ne : k ≠ i) :
      Embedded.matrix (Embedded.sigmaIn k) (M k) ⟨i,x⟩ ⟨j,y⟩ -
        (1 : Matrix (Σ i,β i) (Σ i,β i) ℂ) ⟨i,x⟩ ⟨j,y⟩ = 0 := by
    have off : (⟨i,x⟩ : Σ i,β i) ∉ Set.range (Embedded.sigmaIn k) := by
      rintro ⟨z,eq⟩
      exact ne (congrArg Sigma.fst eq)
    rw [Embedded.matrix_off_row _ _ _ _ off]
    simp only [Matrix.one_apply,sub_self]
  rw [Finset.sum_eq_single i (fun k _ ne => outside k ne) (by simp)]
  by_cases eq : i = j
  · subst j
    have on : Embedded.matrix (Embedded.sigmaIn i) (M i) ⟨i,x⟩ ⟨i,y⟩ = M i x y :=
      Embedded.matrix_on (Embedded.sigmaIn i) (M i) x y
    rw [on]
    simp [Matrix.blockDiagonal'_apply,Matrix.one_apply]
  · have off : (⟨j,y⟩ : Σ i,β i) ∉ Set.range (Embedded.sigmaIn i) := by
      rintro ⟨z,h⟩
      exact eq (congrArg Sigma.fst h)
    rw [Embedded.matrix_off_col _ _ _ _ off]
    simp [Matrix.blockDiagonal'_apply,eq]

/-- Every active local matrix contributes once to the actual union embedding. -/
theorem embedded_blocks_perturbations {σ α : Type} [Fintype σ] [DecidableEq σ]
    [Fintype α] [DecidableEq α]
    {β : σ → Type} [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (e : (Σ i,β i) ↪ α) (M : ∀ i, Matrix (β i) (β i) ℂ) :
    Embedded.matrix e (Matrix.blockDiagonal' M) =
      1 + ∑ i, (Embedded.matrix ((Embedded.sigmaIn i).trans e) (M i) - 1) := by
  rw [blocks_perturbations]
  have eq : ∑ i, (Embedded.matrix (Embedded.sigmaIn i) (M i) - 1) =
      (Finset.univ.toList.map (fun i => Embedded.matrix (Embedded.sigmaIn i) (M i) - 1)).sum := by
    simp
  rw [eq,UniformCalendarRenderAffine.embed_sum_perturbations]
  simp only [Embedded.matrix_comp]
  congr 1
  simp

end
end ExactFourierCircuits.UniformCalendarRenderUnion

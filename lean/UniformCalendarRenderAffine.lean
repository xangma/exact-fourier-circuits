import UniformCalendarRenderTick

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarRenderAffine
noncomputable section
open OAI.ExactFourier

/-- Identity-preserving matrix embedding is affine on perturbations of identity. -/
theorem embed_add_sub_one {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ↪ β) (A B : Matrix α α ℂ) :
    Embedded.matrix e (A + B - 1) = Embedded.matrix e A + Embedded.matrix e B - 1 := by
  ext i j
  by_cases hi : i ∈ Set.range e
  · obtain ⟨a,rfl⟩ := hi
    by_cases hj : j ∈ Set.range e
    · obtain ⟨b,rfl⟩ := hj
      simp only [Matrix.add_apply,Matrix.sub_apply,Embedded.matrix_on]
      congr 1
      simp [Matrix.one_apply,e.injective.eq_iff]
    · simp only [Embedded.matrix_off_col e _ _ _ hj,Matrix.add_apply,Matrix.sub_apply]
      by_cases eq : e a = j <;> simp [Matrix.one_apply,eq]
  · simp only [Embedded.matrix_off_row e _ _ _ hi,Matrix.add_apply,Matrix.sub_apply]
    by_cases eq : i = j <;> simp [Matrix.one_apply,eq]

theorem embed_sum_perturbations {α β ι : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ↪ β) (L : List ι) (f : ι → Matrix α α ℂ) :
    Embedded.matrix e (1 + (L.map (fun i => f i - 1)).sum) =
      1 + (L.map (fun i => Embedded.matrix e (f i) - 1)).sum := by
  induction L with
  | nil => simp [Embedded.matrix_one]
  | cons i L ih =>
    have eq : (1 : Matrix α α ℂ) + (f i - 1 + (L.map (fun j => f j - 1)).sum) =
        f i + (1 + (L.map (fun j => f j - 1)).sum) - 1 := by abel
    simp only [List.map_cons,List.sum_cons]
    rw [eq,embed_add_sub_one,ih]
    abel

theorem blocks_perturbations {a b n : ℕ} (e : (Fin a ⊕ Fin b) ≃ Fin n)
    (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ) :
    Matrix.reindex e e (Matrix.fromBlocks A 0 0 B) =
      Embedded.matrix (Function.Embedding.inl.trans e.toEmbedding) A +
      Embedded.matrix (Function.Embedding.inr.trans e.toEmbedding) B - 1 := by
  rw [← Embedded.matrix_equiv]
  rw [← Embedded.matrix_comp,← Embedded.matrix_comp,← embed_add_sub_one]
  congr 1
  rw [Embedded.matrix_inl,Embedded.matrix_inr]
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.one_apply]

end
end ExactFourierCircuits.UniformCalendarRenderAffine

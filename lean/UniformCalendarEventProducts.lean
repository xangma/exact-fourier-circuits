import UniformGlobalCalendarDispatchTables
import UniformCalendarRenderSnapshot

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarEventProducts
noncomputable section
open OAI.ExactFourier UniformLayerSnapshot UniformGlobalCalendarUnion
open UniformGlobalCalendarDispatch

lemma foldValues_product (es : List Event) (g : ℕ → ℂ) (x : ℕ) :
    foldValues es g x = (es.map (fun e => phaseFactor e.phase e.factor x)).prod * g x := by
  induction es generalizing g with
  | nil => simp [foldValues]
  | cons e es ih =>
    rw [foldValues, ih]
    simp only [List.map_cons, List.prod_cons]
    ring

lemma product_get {α : Type} (xs : List α) (f : α → ℂ) :
    (xs.map f).prod = ∏ i : Fin xs.length, f (xs.get i) := by
  calc
    (xs.map f).prod = (List.ofFn (fun i => f (xs.get i))).prod := by
      rw [List.ofFn_comp', List.ofFn_get]
    _ = _ := List.prod_ofFn

lemma foldValues_perm {es fs : List Event} (h : es.Perm fs) (g : ℕ → ℂ) :
    foldValues es g = foldValues fs g := by
  funext x
  rw [foldValues_product, foldValues_product, (h.map _).prod_eq]

lemma embedded_diagonal_on {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : Snapshot α) (e : α ↪ β) (x : α) :
    (S.embed e).diagonal (e x) = S.diagonal x := by
  change Embedded.matrix e (Matrix.diagonal S.diagonal) (e x) (e x) = _
  rw [Embedded.matrix_on, Matrix.diagonal_apply_eq]

lemma embedded_diagonal_off {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : Snapshot α) (e : α ↪ β) (x : β)
    (h : ∀ y, e y ≠ x) : (S.embed e).diagonal x = 1 := by
  change Embedded.matrix e (Matrix.diagonal S.diagonal) x x = _
  rw [Embedded.matrix_off_row e _ x x (by rintro ⟨y,eq⟩; exact h y eq)]
  simp

lemma family_diagonal_product {σ γ : Type} [Fintype σ] [DecidableEq σ]
    [Fintype γ] [DecidableEq γ] {β : σ → Type}
    [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (S : ∀ i, Snapshot (β i)) (e : (Σ i, β i) ↪ γ) (x : γ) :
    ((UniformGlobalCalendarUnion.Snapshot.family S).embed e).diagonal x =
      ∏ i, ((S i).embed ((Embedded.sigmaIn i).trans e)).diagonal x := by
  classical
  by_cases inside : ∃ y, e y = x
  · rcases inside with ⟨⟨i,y⟩,rfl⟩
    rw [embedded_diagonal_on]
    change (S i).diagonal y = _
    rw [Finset.prod_eq_single i]
    · exact (embedded_diagonal_on (S i) ((Embedded.sigmaIn i).trans e) y).symm
    · intro j _ ne
      apply embedded_diagonal_off
      intro z eq
      have ij : j = i := congrArg Sigma.fst (e.injective eq)
      exact ne ij
    · simp
  · rw [embedded_diagonal_off _ e x (by intro y eq; exact inside ⟨y,eq⟩)]
    symm
    apply Finset.prod_eq_one
    intro i _
    apply embedded_diagonal_off
    intro y eq
    exact inside ⟨⟨i,y⟩,eq⟩

end
end ExactFourierCircuits.UniformCalendarEventProducts

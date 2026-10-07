import BinaryProjection

set_option autoImplicit false

namespace ExactFourierCircuits.ResidualBudget
open BinaryFrames BinaryResiduals BinaryProjection Module
open scoped BigOperators
noncomputable section

universe u
variable {ι : Type u} {κ α ν : Type*} [Fintype ι]

section Rank
variable [Fintype κ] [DecidableEq κ] [Fintype α] [DecidableEq α] [Fintype ν]

/-- The actual nested subspaces decompose into the smaller frame and geometric residual. -/
lemma nested_decomposes (A S : Submodule F2 (Vec ι)) (hAS : A ≤ S)
    (a : Basis κ F2 A) (ha : Orthonormal (fun i => (a i : Vec ι))) :
    Decomposes A (residual A S) S := by
  have h := frameSpan_decomposes_residual (fun i => (a i : Vec ι)) ha S
    (by simpa only [frameSpan, basis_span_coe] using hAS)
  simpa only [frameSpan, basis_span_coe] using h

/-- Residual cardinality is derived from actual bases and actual inclusion. -/
theorem nested_residual_cardinality (A S : Submodule F2 (Vec ι)) (hAS : A ≤ S)
    (a : Basis κ F2 A) (e : Basis α F2 (residual A S)) (s : Basis ν F2 S)
    (ha : Orthonormal (fun i => (a i : Vec ι)))
    (he : Orthonormal (fun i => (e i : Vec ι))) :
    Fintype.card κ + Fintype.card α = Fintype.card ν := by
  have hD := nested_decomposes A S hAS a ha
  let bS := (sumBasis A (residual A S) a e ha he hD.2).map
    (LinearEquiv.ofEq _ _ hD.1)
  calc
    _ = Module.finrank F2 S := by
      rw [Module.finrank_eq_card_basis bS]
      simp
    _ = _ := Module.finrank_eq_card_basis s

end Rank

/-- The schedule API can consume this exact Nat equation without assuming a rank difference. -/
theorem nested_residual_dimension {dA dR dS : ℕ}
    (A S : Submodule F2 (Vec ι)) (hAS : A ≤ S)
    (a : Basis (Fin dA) F2 A) (e : Basis (Fin dR) F2 (residual A S)) (s : Basis (Fin dS) F2 S)
    (ha : Orthonormal (fun i => (a i : Vec ι)))
    (he : Orthonormal (fun i => (e i : Vec ι))) : dA + dR = dS := by
  simpa only [Fintype.card_fin] using nested_residual_cardinality A S hAS a e s ha he

theorem nested_residual_finrank_add {dA dR dS : ℕ}
    (A S : Submodule F2 (Vec ι)) (hAS : A ≤ S)
    (a : Basis (Fin dA) F2 A) (e : Basis (Fin dR) F2 (residual A S)) (s : Basis (Fin dS) F2 S)
    (ha : Orthonormal (fun i => (a i : Vec ι)))
    (he : Orthonormal (fun i => (e i : Vec ι))) :
    Module.finrank F2 A + Module.finrank F2 (residual A S) = Module.finrank F2 S := by
  rw [Module.finrank_eq_card_basis a, Module.finrank_eq_card_basis e, Module.finrank_eq_card_basis s]
  simp only [Fintype.card_fin]
  exact nested_residual_dimension A S hAS a e s ha he

/-- Any basis of the actual central residual has exactly the coordinate-space dimension. -/
theorem central_edge_dimension {η : Type*} [Fintype η] [DecidableEq η] {dR : ℕ}
    (B E : Submodule F2 (Vec ι)) (p : Vec ι)
    (hE : Decomposes B (line p) E) (hp : dot p p = 1)
    (hsmall : Nondegenerate (label1 (η := η) B))
    (e : Basis (Fin dR) F2 (residual (label1 (η := η) B) (label3 (η := η) E))) :
    dR = Fintype.card η := by
  calc
    dR = Module.finrank F2 (residual (label1 (η := η) B) (label3 (η := η) E)) := by
      simpa only [Fintype.card_fin] using (Module.finrank_eq_card_basis e).symm
    _ = Fintype.card η := central_decrease_dimension B E p hE hp hsmall

/-- A future unit line preserves the actual central residual basis size, including an empty tensor. -/
theorem central_future_edge_dimension {η ζ : Type*} [Fintype η] [DecidableEq η]
    [Fintype ζ] {dR : ℕ} (B E : Submodule F2 (Vec ι)) (p : Vec ι) (q : Vec ζ)
    (hE : Decomposes B (line p) E) (hp : dot p p = 1) (hq : dot q q = 1)
    (hsmall : Nondegenerate (tensorSpace (label1 (η := η) B) (line q)))
    (e : Basis (Fin dR) F2 (residual (tensorSpace (label1 (η := η) B) (line q))
      (tensorSpace (label3 (η := η) E) (line q)))) : dR = Fintype.card η := by
  calc
    dR = Module.finrank F2 (residual (tensorSpace (label1 (η := η) B) (line q))
        (tensorSpace (label3 (η := η) E) (line q))) := by
      simpa only [Fintype.card_fin] using (Module.finrank_eq_card_basis e).symm
    _ = Fintype.card η := central_future_decrease_dimension B E p q hE hp hq hsmall

/-- A geometric certificate contains an orthonormal basis of the actual residual in the correct direction. -/
inductive GeometricEdge (A S : Submodule F2 (Vec ι)) (d : ℕ) : Bool → Type u
  | increasing (nested : A ≤ S) (basis : Basis (Fin d) F2 (residual A S))
      (orthonormal : Orthonormal (fun i => (basis i : Vec ι))) : GeometricEdge A S d false
  | decreasing (nested : S ≤ A) (basis : Basis (Fin d) F2 (residual S A))
      (orthonormal : Orthonormal (fun i => (basis i : Vec ι))) : GeometricEdge A S d true

/-- One edge's nontruncated signed-change accounting. -/
lemma step_accounting {before after residualDim : ℕ} (decreasing : Bool)
    (h : if decreasing then after + residualDim = before else before + residualDim = after) :
    residualDim + before = after + 2 * (if decreasing then residualDim else 0) := by
  cases decreasing <;> simp_all <;> omega

lemma geometric_edge_accounting {dA dS dR : ℕ} {decreasing : Bool}
    (A S : Submodule F2 (Vec ι))
    (a : Basis (Fin dA) F2 A) (s : Basis (Fin dS) F2 S)
    (ha : Orthonormal (fun i => (a i : Vec ι)))
    (hs : Orthonormal (fun i => (s i : Vec ι))) (edge : GeometricEdge A S dR decreasing) :
    dR + dA = dS + 2 * (if decreasing then dR else 0) := by
  cases edge with
  | increasing hAS e he =>
    have h := nested_residual_dimension A S hAS a e s ha he
    simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero]
    omega
  | decreasing hSA e he =>
    have h := nested_residual_dimension S A hSA s e a hs he
    simp only [↓reduceIte]
    omega

/-- Concatenating two continuous certified budgets cancels the shared endpoint. -/
lemma budget_comp {r₁ r₂ source middle sink loss₁ loss₂ : ℕ}
    (h₁ : r₁ + source = middle + 2 * loss₁) (h₂ : r₂ + middle = sink + 2 * loss₂) :
    r₁ + r₂ + source = sink + 2 * (loss₁ + loss₂) := by omega

/-- Exact telescoping for a finite path, including an empty path. -/
lemma finite_path_accounting {k : ℕ} (dimension : Fin (k + 1) → ℕ)
    (residualDim decreaseDim : Fin k → ℕ)
    (hstep : ∀ i, residualDim i + dimension i.castSucc = dimension i.succ + 2 * decreaseDim i) :
    (∑ i, residualDim i) + dimension 0 = dimension (Fin.last k) + 2 * ∑ i, decreaseDim i := by
  have hsum : (∑ i : Fin k, (residualDim i + dimension i.castSucc)) =
      (∑ i : Fin k, (dimension i.succ + 2 * decreaseDim i)) :=
    Finset.sum_congr rfl (fun i hi => hstep i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hfirst := Fin.sum_univ_succ dimension
  have hlast := Fin.sum_univ_castSucc dimension
  omega

/-- Every residual dimension in this path comes from a basis of the actual geometric residual. -/
theorem geometric_frame_path_budget {k : ℕ}
    (space : Fin (k + 1) → Submodule F2 (Vec ι)) (dimension : Fin (k + 1) → ℕ)
    (basis : ∀ j, Basis (Fin (dimension j)) F2 (space j))
    (orthonormal : ∀ j, Orthonormal (fun i => (basis j i : Vec ι)))
    (residualDim : Fin k → ℕ) (decreasing : Fin k → Bool)
    (edge : ∀ i, GeometricEdge (space i.castSucc) (space i.succ) (residualDim i) (decreasing i)) :
    (∑ i, residualDim i) + dimension 0 = dimension (Fin.last k) +
      2 * ∑ i, if decreasing i then residualDim i else 0 := by
  apply finite_path_accounting
  intro i
  exact geometric_edge_accounting _ _ (basis i.castSucc) (basis i.succ)
    (orthonormal i.castSucc) (orthonormal i.succ) (edge i)

/-- Adding continuous role budgets preserves the exact nontruncated balance. -/
lemma role_budget_sum {β : Type*} [Fintype β]
    (residualTotal sourceDim sinkDim decreaseTotal : β → ℕ)
    (h : ∀ j, residualTotal j + sourceDim j = sinkDim j + 2 * decreaseTotal j) :
    (∑ j, residualTotal j) + (∑ j, sourceDim j) =
      (∑ j, sinkDim j) + 2 * ∑ j, decreaseTotal j := by
  have he : (∑ j : β, (residualTotal j + sourceDim j)) =
      (∑ j : β, (sinkDim j + 2 * decreaseTotal j)) :=
    Finset.sum_congr rfl (fun j hj => h j)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using he

/-- Once each actual central residual is identified, its finite sum counts the actual events. -/
lemma uniform_decrease_total {β : Type*} [Fintype β] (decreaseDim : β → ℕ) (height : ℕ)
    (h : ∀ j, decreaseDim j = height) : (∑ j, decreaseDim j) = Fintype.card β * height := by
  simp only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- A whole finite family of role paths, with certified actual subspaces at every endpoint. -/
theorem geometric_role_paths_budget {β : Type*} [Fintype β] {k : ℕ}
    (space : β → Fin (k + 1) → Submodule F2 (Vec ι)) (dimension : β → Fin (k + 1) → ℕ)
    (basis : ∀ j t, Basis (Fin (dimension j t)) F2 (space j t))
    (orthonormal : ∀ j t, Orthonormal (fun i => (basis j t i : Vec ι)))
    (residualDim : β → Fin k → ℕ) (decreasing : β → Fin k → Bool)
    (edge : ∀ j i, GeometricEdge (space j i.castSucc) (space j i.succ)
      (residualDim j i) (decreasing j i)) :
    (∑ j, ∑ i, residualDim j i) + (∑ j, dimension j 0) =
      (∑ j, dimension j (Fin.last k)) +
      2 * ∑ j, ∑ i, if decreasing j i then residualDim j i else 0 := by
  apply role_budget_sum
  intro j
  exact geometric_frame_path_budget (space j) (dimension j) (basis j) (orthonormal j)
    (residualDim j) (decreasing j) (edge j)

/-- Terminal dimensions and total losses specialize the geometric path balance. -/
lemma network_residual_balance {residualTotal sourceDim sinkDim decreaseTotal W m N₀ : ℕ}
    (hpath : residualTotal + sourceDim = sinkDim + 2 * decreaseTotal)
    (hsource : sourceDim = N₀) (hterminal : sinkDim + N₀ = W * m) :
    residualTotal + 2 * N₀ = W * m + 2 * decreaseTotal := by omega

/-- This recovers the paper's subtraction formula only after proving the nontruncated balance. -/
lemma network_residual_formula {residualTotal decreaseTotal W m N₀ : ℕ}
    (hbalance : residualTotal + 2 * N₀ = W * m + 2 * decreaseTotal)
    (hterminal : 2 * N₀ ≤ W * m) :
    residualTotal = W * m - 2 * N₀ + 2 * decreaseTotal := by omega

/-- The margin becomes an exact saving balance; concrete graph losses remain an input. -/
lemma residual_saving_balance {residualTotal decreaseTotal W m N₀ Δ : ℕ}
    (hbalance : residualTotal + 2 * N₀ = W * m + 2 * decreaseTotal)
    (hmargin : Δ + 2 * decreaseTotal = 2 * N₀) : residualTotal + Δ = W * m := by omega

end
end ExactFourierCircuits.ResidualBudget

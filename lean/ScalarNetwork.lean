import ProjectionIdentities
set_option autoImplicit false

/- The companion paper's actual triple-incidence maps. This establishes the
   scalar invocation, including dirty auxiliaries, independently of its frames. -/
namespace ExactFourierCircuits.ScalarNetwork
open scoped BigOperators
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev Triple (α : Type*) := {s : Finset α // s.card = 3}

def neighboring (S T : Triple α) : Prop := (S.val ∩ T.val).card % 2 = 0

instance (S T : Triple α) : Decidable (neighboring S T) :=
  inferInstanceAs (Decidable ((S.val ∩ T.val).card % 2 = 0))

abbrev Edge (α : Type*) [DecidableEq α] :=
  {p : Triple α × Triple α // neighboring p.1 p.2}

def coefficient (S T : Triple α) : ℂ := ((S.val ∩ T.val).card - (1 : ℂ)) / 2

def G : Matrix (Option α) (Triple α) ℂ :=
  Matrix.of fun i T => match i with
    | none => 1
    | some j => if j ∈ T.val then 1 else 0

def R : Matrix (Triple α) (Option α) ℂ :=
  Matrix.of fun S i => match i with
    | none => -1 / 2
    | some j => if j ∈ S.val then 1 / 2 else 0

def V : Matrix (Edge α) (Triple α) ℂ :=
  Matrix.of fun e T => if e.val.2 = T then 1 else 0

def J : Matrix (Triple α) (Edge α) ℂ :=
  Matrix.of fun S e => if e.val.1 = S then -coefficient S e.val.2 else 0

/-- Explicit rectangular composition avoids an ambiguous type-copy HMul instance. -/
def composeMatrix {κ β μ : Type*} [Fintype β]
    (M : Matrix κ β ℂ) (N : Matrix β μ ℂ) : Matrix κ μ ℂ :=
  Matrix.of fun i k => ∑ j, M i j * N j k

theorem composeMatrix_mulVec {κ β μ : Type*} [Fintype β] [Fintype μ]
    (M : Matrix κ β ℂ) (N : Matrix β μ ℂ) (x : μ → ℂ) :
    (composeMatrix M N).mulVec x = M.mulVec (N.mulVec x) := by
  funext i
  simp only [composeMatrix, Matrix.of_apply, Matrix.mulVec, dotProduct,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem RG_entry (S T : Triple α) :
    composeMatrix R G S T = coefficient S T := by
  have hsum : (∑ j : α, (if j ∈ S.val then (1 / 2 : ℂ) else 0) *
      (if j ∈ T.val then 1 else 0)) = ((S.val ∩ T.val).card : ℂ) / 2 := by
    calc
      _ = ∑ j : α, if j ∈ S.val ∩ T.val then (1 / 2 : ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hs : j ∈ S.val <;> by_cases ht : j ∈ T.val <;> simp [hs, ht]
      _ = ((S.val ∩ T.val).card : ℂ) / 2 := by
        simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
        ring
  simp only [composeMatrix, Matrix.of_apply, Fintype.sum_option, R, G]
  rw [hsum]
  unfold coefficient
  ring

theorem JV_entry (S T : Triple α) :
    composeMatrix J V S T =
      if neighboring S T then -coefficient S T else 0 := by
  have hterm : ∀ e : Edge α, J S e * V e T =
      if e.val = (S, T) then -coefficient S T else 0 := by
    rintro ⟨⟨S', T'⟩, hn⟩
    by_cases hs : S' = S <;> by_cases ht : T' = T <;> simp [J, V, hs, ht, Prod.ext_iff]
  simp only [composeMatrix, Matrix.of_apply, hterm]
  by_cases hn : neighboring S T
  · let e : Edge α := ⟨(S, T), hn⟩
    have he : ∀ e' : Edge α, e'.val = (S, T) ↔ e' = e := by
      intro e'
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    simp only [he]
    simp [hn]
  · have hz : ∀ e : Edge α, e.val ≠ (S, T) := by
      intro e he
      have hp : neighboring e.val.1 e.val.2 := e.property
      rw [he] at hp
      exact hn hp
    simp [hn, hz]

omit [Fintype α] in
lemma intersection_card_three_iff (S T : Triple α) :
    (S.val ∩ T.val).card = 3 ↔ S = T := by
  constructor
  · intro hc
    have hs : S.val ∩ T.val = S.val :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [S.property, hc])
    have ht : S.val ∩ T.val = T.val :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [T.property, hc])
    exact Subtype.ext (hs.symm.trans ht)
  · rintro rfl
    simpa using S.property

/-- The cancellation RG+JV=I uses actual ordered neighbor edges, not extra wires. -/
theorem incidence_identity : composeMatrix R G + composeMatrix J V =
    (1 : Matrix (Triple α) (Triple α) ℂ) := by
  ext S T
  rw [Matrix.add_apply, RG_entry, JV_entry]
  by_cases hst : S = T
  · subst T
    norm_num [coefficient, neighboring, S.property, Matrix.one_apply]
  · have hle : (S.val ∩ T.val).card ≤ 3 := by
      calc
        _ ≤ S.val.card := Finset.card_le_card Finset.inter_subset_left
        _ = 3 := S.property
    have hne : (S.val ∩ T.val).card ≠ 3 := by
      intro h
      exact hst ((intersection_card_three_iff S T).mp h)
    have hlt : (S.val ∩ T.val).card ≤ 2 := by omega
    interval_cases hc : (S.val ∩ T.val).card <;>
      norm_num [coefficient, neighboring, hc, Matrix.one_apply, hst]

theorem incidence_linear_identity :
    (Matrix.mulVecLin (R (α := α))).comp (Matrix.mulVecLin G) +
      (Matrix.mulVecLin J).comp (Matrix.mulVecLin V) =
        (LinearMap.id : (Triple α → ℂ) →ₗ[ℂ] (Triple α → ℂ)) := by
  apply LinearMap.ext
  intro x
  funext i
  change (R.mulVec (G.mulVec x) + J.mulVec (V.mulVec x)) i = x i
  rw [← composeMatrix_mulVec, ← composeMatrix_mulVec, ← Matrix.add_mulVec,
    incidence_identity (α := α), Matrix.one_mulVec]

/-- Every initial side and central value is restored, without a zero-data hypothesis. -/
theorem invocation_dirty_identity (ε : ℂ)
    (s : Projection.DirtyState (Triple α → ℂ) (Edge α → ℂ) (Option α → ℂ)) :
    Projection.eightRows ε (Matrix.mulVecLin (V (α := α))) (Matrix.mulVecLin G)
      (Matrix.mulVecLin J) (Matrix.mulVecLin R) s =
        ⟨s.x, s.y + ε • s.x, s.auxiliaryA, s.auxiliaryC⟩ :=
  Projection.eightRows_identity ε _ _ _ _ incidence_linear_identity s

omit [Fintype α] in
theorem neighboring_iff (S T : Triple α) :
    neighboring S T ↔ (S.val ∩ T.val).card = 0 ∨ (S.val ∩ T.val).card = 2 := by
  have hle : (S.val ∩ T.val).card ≤ 3 := by
    calc
      _ ≤ S.val.card := Finset.card_le_card Finset.inter_subset_left
      _ = 3 := S.property
  unfold neighboring
  omega

omit [Fintype α] in
theorem neighboring_even (S T : Triple α) (hn : neighboring S T) :
    Even (S.val ∩ T.val).card := Nat.even_iff.mpr hn

omit [Fintype α] in
theorem neighboring_distinct (S T : Triple α) (hn : neighboring S T) : S ≠ T := by
  intro h
  subst T
  norm_num [neighboring, S.property] at hn

omit [DecidableEq α] in
theorem triple_card : Fintype.card (Triple α) = Nat.choose (Fintype.card α) 3 := by
  have he : Fintype.card (Triple α) = (Finset.univ.powersetCard 3 : Finset (Finset α)).card :=
    Fintype.card_of_subtype _ (by intro s; simp)
  rw [he, Finset.card_powersetCard, Finset.card_univ]

end
end ExactFourierCircuits.ScalarNetwork

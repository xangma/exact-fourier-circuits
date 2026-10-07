import TripleCounting

/- Counts of the actual nonzero coefficients in the eight scalar rows. -/
namespace ExactFourierCircuits.ScalarSupport
open ScalarNetwork TripleCounting
open scoped BigOperators
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev Support {ι κ : Type*} (M : Matrix ι κ ℂ) :=
  {p : ι × κ // M p.1 p.2 ≠ 0}

omit [Fintype α] in
theorem neighbor_coefficient_ne_zero (S T : Triple α) (h : neighboring S T) :
    coefficient S T ≠ 0 := by
  rcases (neighboring_iff S T).mp h with hc | hc <;> norm_num [coefficient, hc]

omit [Fintype α] in
theorem G_nonzero (i : Option α) (T : Triple α) :
    G i T ≠ 0 ↔ match i with | none => True | some j => j ∈ T.val := by
  cases i with
  | none => simp [G]
  | some j => by_cases hj : j ∈ T.val <;> simp [G, hj]

omit [Fintype α] in
theorem R_nonzero (T : Triple α) (i : Option α) : R T i ≠ 0 ↔ G i T ≠ 0 := by
  cases i with
  | none => norm_num [R, G]
  | some j => by_cases hj : j ∈ T.val <;> norm_num [R, G, hj]

omit [Fintype α] in
theorem V_nonzero (e : Edge α) (T : Triple α) : V e T ≠ 0 ↔ T = e.val.2 := by
  by_cases h : T = e.val.2 <;> simp [V, h, eq_comm]

omit [Fintype α] in
theorem J_nonzero (T : Triple α) (e : Edge α) : J T e ≠ 0 ↔ T = e.val.1 := by
  have hc := neighbor_coefficient_ne_zero e.val.1 e.val.2 e.property
  by_cases h : T = e.val.1 <;> simp [J, h, hc, eq_comm]

abbrev Incidence := (T : Triple α) × Option {j : α // j ∈ T.val}

def incidenceEquiv : Support (G (α := α)) ≃ Incidence (α := α) where
  toFun p := match hi : p.val.1 with
    | none => ⟨p.val.2, none⟩
    | some j => ⟨p.val.2, some ⟨j, by
        have h := (G_nonzero p.val.1 p.val.2).mp p.property
        simpa only [hi] using h⟩⟩
  invFun p := match p.2 with
    | none => ⟨(none, p.1), by simp [G]⟩
    | some j => ⟨(some j.val, p.1), by simp [G, j.property]⟩
  left_inv p := by
    rcases p with ⟨⟨i, T⟩, hp⟩
    cases i <;> apply Subtype.ext <;> rfl
  right_inv p := by
    rcases p with ⟨T, i⟩
    cases i <;> rfl

theorem G_support_card : Fintype.card (Support (G (α := α))) =
    4 * Nat.choose (Fintype.card α) 3 := by
  rw [Fintype.card_congr (incidenceEquiv (α := α)), Fintype.card_sigma]
  have hc (T : Triple α) : Fintype.card (Option {j : α // j ∈ T.val}) = 4 := by
    rw [Fintype.card_option, Fintype.card_coe, T.property]
  simp only [hc, Finset.sum_const, Finset.card_univ, triple_card, nsmul_eq_mul]
  simp only [Nat.cast_id, Nat.mul_comm]

def R_support_equiv : Support (R (α := α)) ≃ Support (G (α := α)) where
  toFun p := ⟨(p.val.2, p.val.1), (R_nonzero _ _).mp p.property⟩
  invFun p := ⟨(p.val.2, p.val.1), (R_nonzero _ _).mpr p.property⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

theorem R_support_card : Fintype.card (Support (R (α := α))) =
    4 * Nat.choose (Fintype.card α) 3 := by
  rw [Fintype.card_congr (R_support_equiv (α := α)), G_support_card]

def V_support_equiv : Support (V (α := α)) ≃ Edge α where
  toFun p := p.val.1
  invFun e := ⟨(e, e.val.2), (V_nonzero _ _).mpr rfl⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl ((V_nonzero _ _).mp p.property).symm
  right_inv e := rfl

def J_support_equiv : Support (J (α := α)) ≃ Edge α where
  toFun p := p.val.2
  invFun e := ⟨(e.val.1, e), (J_nonzero _ _).mpr rfl⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext ((J_nonzero _ _).mp p.property).symm rfl
  right_inv e := rfl

theorem V_support_card : Fintype.card (Support (V (α := α))) =
    Nat.choose (Fintype.card α) 3 * neighborDegree (Fintype.card α) := by
  rw [Fintype.card_congr (V_support_equiv (α := α)), edge_card]

theorem J_support_card : Fintype.card (Support (J (α := α))) =
    Nat.choose (Fintype.card α) 3 * neighborDegree (Fintype.card α) := by
  rw [Fintype.card_congr (J_support_equiv (α := α)), edge_card]

/-- Every map occurs twice among the eight chronological rows. -/
theorem invocation_support_count :
    2 * (Fintype.card (Support (J (α := α))) + Fintype.card (Support (R (α := α))) +
         Fintype.card (Support (V (α := α))) + Fintype.card (Support (G (α := α)))) =
      4 * Nat.choose (Fintype.card α) 3 * neighborDegree (Fintype.card α) +
        16 * Nat.choose (Fintype.card α) 3 := by
  rw [J_support_card, R_support_card, V_support_card, G_support_card]
  ring

end
end ExactFourierCircuits.ScalarSupport

import TripleNetwork

namespace ExactFourierCircuits.TripleCounting
noncomputable section
open ScalarNetwork
open scoped BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev Subsets (s : Finset α) (k : ℕ) := {t : Finset α // t ⊆ s ∧ t.card = k}
abbrev IntersectionTriples (S : Triple α) (k : ℕ) :=
  {T : Triple α // (S.val ∩ T.val).card = k}

def outside (S : Triple α) : Finset α := Finset.univ \ S.val

theorem subsets_card (s : Finset α) (k : ℕ) :
    Fintype.card (Subsets s k) = Nat.choose s.card k := by
  have he : Fintype.card (Subsets s k) = (s.powersetCard k).card :=
    Fintype.card_of_subtype _ (by intro t; simp)
  rw [he, Finset.card_powersetCard]

theorem outside_card (S : Triple α) : (outside S).card = Fintype.card α - 3 := by
  rw [outside, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, S.property]

omit [DecidableEq α] in
theorem ambient_card_ge_three (S : Triple α) : 3 ≤ Fintype.card α := by
  simpa [S.property] using Finset.card_le_card (Finset.subset_univ S.val)

theorem subsets_disjoint (S : Triple α) {k l : ℕ}
    (A : Subsets S.val k) (B : Subsets (outside S) l) : Disjoint A.val B.val := by
  refine Finset.disjoint_left.mpr ?_
  intro x hxA hxB
  exact (Finset.mem_sdiff.mp (B.property.1 hxB)).2 (A.property.1 hxA)

theorem inside_union (S : Triple α) {k l : ℕ}
    (A : Subsets S.val k) (B : Subsets (outside S) l) : S.val ∩ (A.val ∪ B.val) = A.val := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · intro h
    rcases h.2 with ha | hb
    · exact ha
    · exact False.elim ((Finset.mem_sdiff.mp (B.property.1 hb)).2 h.1)
  · intro ha
    exact ⟨A.property.1 ha, Or.inl ha⟩

theorem outside_union (S : Triple α) {k l : ℕ}
    (A : Subsets S.val k) (B : Subsets (outside S) l) : (A.val ∪ B.val) \ S.val = B.val := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · intro h
    rcases h.1 with ha | hb
    · exact False.elim (h.2 (A.property.1 ha))
    · exact hb
  · intro hb
    exact ⟨Or.inr hb, (Finset.mem_sdiff.mp (B.property.1 hb)).2⟩

def splitTriple (S : Triple α) (k : ℕ) (T : IntersectionTriples S k) :
    Subsets S.val k × Subsets (outside S) (3 - k) :=
  (⟨S.val ∩ T.val.val, Finset.inter_subset_left, T.property⟩,
   ⟨T.val.val \ S.val, by
      constructor
      · intro x hx
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
      · rw [Finset.card_sdiff, T.val.property, T.property]⟩)

def combineTriple (S : Triple α) (k : ℕ) (hk : k ≤ 3)
    (P : Subsets S.val k × Subsets (outside S) (3 - k)) : IntersectionTriples S k :=
  ⟨⟨P.1.val ∪ P.2.val, by
      rw [Finset.card_union_of_disjoint (subsets_disjoint S P.1 P.2), P.1.property.2, P.2.property.2]
      omega⟩, by rw [inside_union S P.1 P.2, P.1.property.2]⟩

/-- A triple with k selected points is exactly k inside points and 3-k outside points. -/
def splitTripleEquiv (S : Triple α) (k : ℕ) (hk : k ≤ 3) :
    IntersectionTriples S k ≃ (Subsets S.val k × Subsets (outside S) (3 - k)) where
  toFun := splitTriple S k
  invFun := combineTriple S k hk
  left_inv T := by
    apply Subtype.ext
    apply Subtype.ext
    change (S.val ∩ T.val.val) ∪ (T.val.val \ S.val) = T.val.val
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  right_inv P := by
    apply Prod.ext
    · apply Subtype.ext
      exact inside_union S P.1 P.2
    · apply Subtype.ext
      exact outside_union S P.1 P.2

theorem intersection_triples_card (S : Triple α) (k : ℕ) (hk : k ≤ 3) :
    Fintype.card (IntersectionTriples S k) =
      Nat.choose 3 k * Nat.choose (Fintype.card α - 3) (3 - k) := by
  rw [Fintype.card_congr (splitTripleEquiv S k hk), Fintype.card_prod,
    subsets_card, subsets_card, S.property, outside_card]

abbrev Neighbors (S : Triple α) := {T : Triple α // neighboring S T}

def neighborDegree (h : ℕ) : ℕ := Nat.choose (h - 3) 3 + 3 * (h - 3)

theorem neighboring_degree (S : Triple α) :
    Fintype.card (Neighbors S) = neighborDegree (Fintype.card α) := by
  let e : Neighbors S ≃ {T : Triple α //
      (S.val ∩ T.val).card = 0 ∨ (S.val ∩ T.val).card = 2} :=
    Equiv.subtypeEquivRight (fun T => neighboring_iff S T)
  rw [Fintype.card_congr e]
  have hd : Disjoint (fun T : Triple α => (S.val ∩ T.val).card = 0)
      (fun T : Triple α => (S.val ∩ T.val).card = 2) := by
    intro f hf hg T hT
    have h0 := hf T hT
    have h2 := hg T hT
    omega
  rw [Fintype.card_subtype_or_disjoint _ _ hd]
  change Fintype.card (IntersectionTriples S 0) + Fintype.card (IntersectionTriples S 2) = _
  rw [intersection_triples_card S 0 (by omega), intersection_triples_card S 2 (by omega)]
  simp [neighborDegree]

def edgeEquiv : Edge α ≃ (Σ S : Triple α, Neighbors S) where
  toFun e := ⟨e.val.1, ⟨e.val.2, e.property⟩⟩
  invFun e := ⟨(e.1, e.2.val), e.2.property⟩
  left_inv e := by cases e; rfl
  right_inv e := by rcases e with ⟨S, T, h⟩; rfl

theorem edge_card : Fintype.card (Edge α) =
    Nat.choose (Fintype.card α) 3 * neighborDegree (Fintype.card α) := by
  rw [Fintype.card_congr (edgeEquiv (α := α)), Fintype.card_sigma]
  simp [neighboring_degree]

/-- Two main banks and the actual fresh side/center roles at every axis/profile. -/
abbrev Role (α : Type*) [DecidableEq α] :=
  (Fin 2 × TripleNetwork.Bank α) ⊕
    (Σ p : Fin 3, TripleNetwork.Profile α p × (Edge α ⊕ Option α))

theorem role_card : Fintype.card (Role α) =
    2 * (Nat.choose (Fintype.card α) 3) ^ 3 +
      3 * (Nat.choose (Fintype.card α) 3) ^ 2 *
        (Nat.choose (Fintype.card α) 3 * neighborDegree (Fintype.card α) + Fintype.card α + 1) := by
  simp only [Role, Fintype.card_sum, Fintype.card_prod, Fintype.card_sigma,
    Fintype.card_fin, TripleNetwork.bank_card, TripleNetwork.profile_card, edge_card,
    Fintype.card_option]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end
end ExactFourierCircuits.TripleCounting

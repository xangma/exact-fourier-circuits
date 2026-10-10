import DFTModelSectorMapBitsPack

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSectorMapBits
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

theorem packed_mod (m : Tape ℕ) (s n k : ℕ) (hk : k ≤ n) :
    packed m s n % 2^k = packed m s k := by
  induction n generalizing k with
  | zero =>
    have he : k = 0 := by omega
    subst k
    simp [packed]
  | succ n ih =>
    by_cases he : k = n+1
    · subst k
      exact Nat.mod_eq_of_lt (packed_bound m s (n+1))
    · have hkn : k ≤ n := by omega
      have hd : 2^k ∣ 2^n := Nat.pow_dvd_pow 2 hkn
      rw [packed, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hd]
      simp only [zero_mul, Nat.zero_mod, Nat.add_zero]
      rw [ih k hkn, Nat.mod_eq_of_lt (packed_bound m s k)]

/-- `h` is zero when no marker exists, otherwise one plus the nearest marker index. -/
def Nearest (m : Tape ℕ) (s n h : ℕ) : Prop :=
  (h = 0 ∧ ∀ i < n, m.look (s+i) 0 = 0) ∨
    ∃ i < n, h = i+1 ∧ m.look (s+i) 0 ≠ 0 ∧
      ∀ j, i < j → j < n → m.look (s+j) 0 = 0

theorem high_packed_last (m : Tape ℕ) (s n : ℕ) (hm : m.look (s+n) 0 ≠ 0) :
    high (packed m s (n+1)) = n+1 := by
  have hf : flag (m.look (s+n) 0) = 1 := by simp [flag, Nat.pos_of_ne_zero hm]
  have hp := Nat.two_pow_pos n
  have hnz : packed m s (n+1) ≠ 0 := by rw [packed, hf]; simp only [mul_one]; omega
  have hl : Nat.log2 (packed m s (n+1)) = n := (Nat.log2_eq_iff hnz).2
    ⟨by rw [packed, hf]; simp only [mul_one]; omega, packed_bound m s (n+1)⟩
  simp [high, hnz, hl]

theorem high_packed_nearest (m : Tape ℕ) (s n : ℕ) :
    Nearest m s n (high (packed m s n)) := by
  induction n with
  | zero => exact Or.inl ⟨by simp [packed, high], by omega⟩
  | succ n ih =>
    by_cases hm : m.look (s+n) 0 = 0
    · have he : packed m s (n+1) = packed m s n := by simp [packed, hm, flag]
      rw [he]
      rcases ih with hnone | ⟨i, hin, hhi, hmi, hmax⟩
      · apply Or.inl
        refine ⟨hnone.1, ?_⟩
        intro i hi
        by_cases hie : i = n
        · simpa [hie] using hm
        · exact hnone.2 i (by omega)
      · apply Or.inr
        refine ⟨i, by omega, hhi, hmi, ?_⟩
        intro j hij hj
        by_cases hje : j = n
        · simpa [hje] using hm
        · exact hmax j hij (by omega)
    · apply Or.inr
      exact ⟨n, by omega, high_packed_last m s n hm, hm, by omega⟩

theorem high_packed_zero_iff (m : Tape ℕ) (s n : ℕ) :
    high (packed m s n) = 0 ↔ ∀ i < n, m.look (s+i) 0 = 0 := by
  have h := high_packed_nearest m s n
  constructor
  · intro hz
    rcases h with hh | ⟨i, _, hi, _, _⟩
    · exact hh.2
    · omega
  · intro hall
    rcases h with hh | ⟨i, hin, _, hi, _⟩
    · exact hh.1
    · exact False.elim (hi (hall i hin))

theorem high_prefix_nearest (m : Tape ℕ) (s b t : ℕ) (ht : t < b) :
    Nearest m s (t+1) (high (packed m s b % 2^(t+1))) := by
  rw [packed_mod m s b (t+1) (by omega)]
  exact high_packed_nearest m s (t+1)

theorem highTable_lookup (b z : ℕ) (hz : z < 2^b) :
    (run highTable b).val.look z 0 = high z := by
  rw [highTable_value]
  simp [Tape.look, Tape.tab, hz]

theorem pack_lookup (b V : ℕ) (m : Tape ℕ) (c : ℕ) (hc : c < V/b+1) :
    (run pack (b,(V,m))).val.look c 0 = packed m (c*b) b := by
  rw [pack_value]
  simp [Tape.look, Tape.tab, hc]

/-- The two genuinely produced tables decode the nearest marker in the current block prefix. -/
theorem produced_prefix_nearest (b V : ℕ) (m : Tape ℕ) (c t : ℕ)
    (hc : c < V/b+1) (ht : t < b) :
    Nearest m (c*b) (t+1)
      ((run highTable b).val.look
        ((run pack (b,(V,m))).val.look c 0 % 2^(t+1)) 0) := by
  rw [pack_lookup b V m c hc]
  have hp : packed m (c*b) b % 2^(t+1) < 2^b := by
    exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos (t+1)))
      (Nat.pow_le_pow_right (by decide) (by omega))
  rw [highTable_lookup b _ hp]
  exact high_prefix_nearest m (c*b) b t ht

theorem produced_prefix_zero_iff (b V : ℕ) (m : Tape ℕ) (c t : ℕ)
    (hc : c < V/b+1) (ht : t < b) :
    (run highTable b).val.look
      ((run pack (b,(V,m))).val.look c 0 % 2^(t+1)) 0 = 0 ↔
        ∀ i ≤ t, m.look (c*b+i) 0 = 0 := by
  rw [pack_lookup b V m c hc]
  have hp : packed m (c*b) b % 2^(t+1) < 2^b := by
    exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos (t+1)))
      (Nat.pow_le_pow_right (by decide) (by omega))
  rw [highTable_lookup b _ hp, packed_mod m (c*b) b (t+1) (by omega), high_packed_zero_iff]
  simp only [Nat.lt_succ_iff]

end
end ExactFourierCircuits.DFTModelSectorMapBits

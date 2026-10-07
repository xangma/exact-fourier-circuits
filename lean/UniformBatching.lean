import UniformExponent
import Mathlib.Data.Nat.Log

/- Exact batching and quotient-chain estimates. Operational recurrence bounds remain premises. -/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformBatching
noncomputable section

def blockSize : ℕ := ExplicitSeedBudget.m
def roleBits : ℕ := ExplicitSeedBudget.roleBits
def width : ℕ := ExplicitSeedBudget.paddedRoles
def threshold : ℕ := blockSize * (roleBits + 1)
def quotient (k : ℕ) : ℕ := k / blockSize
def remainder (k : ℕ) : ℕ := k % blockSize
def fiberCount (k : ℕ) : ℕ := 2 ^ (k - quotient k)
def batchCount (k : ℕ) : ℕ := 2 ^ (k - quotient k - roleBits)

theorem blockSize_eq : blockSize = 1000000 := rfl
theorem roleBits_eq : roleBits = 71 := rfl
theorem blockSize_pos : 0 < blockSize := by rw [blockSize_eq]; norm_num
theorem one_lt_blockSize : 1 < blockSize := by rw [blockSize_eq]; norm_num
theorem threshold_pos : 0 < threshold := Nat.mul_pos blockSize_pos (Nat.succ_pos roleBits)
theorem width_eq_pow : width = 2 ^ roleBits := ExplicitSeedBudget.padding.1
theorem blockSize_cast : (blockSize : ℝ) = UniformExponent.m := rfl

theorem quotient_remainder (k : ℕ) : k = blockSize * quotient k + remainder k := by
  unfold quotient remainder
  exact (Nat.div_add_mod k blockSize).symm

theorem remainder_lt (k : ℕ) : remainder k < blockSize := Nat.mod_lt k blockSize_pos

theorem quotient_large {k : ℕ} (hk : threshold ≤ k) : 72 ≤ quotient k := by
  unfold quotient
  apply (Nat.le_div_iff_mul_le blockSize_pos).2
  simpa only [threshold, roleBits_eq, Nat.reduceAdd, Nat.mul_comm] using hk

theorem quotient_pos {k : ℕ} (hk : threshold ≤ k) : 0 < quotient k := by
  have h := quotient_large hk
  omega

theorem quotient_lt {k : ℕ} (hk : threshold ≤ k) : quotient k < k := by
  exact Nat.div_lt_self (threshold_pos.trans_le hk) one_lt_blockSize

theorem fiber_exponent_large {k : ℕ} (hk : threshold ≤ k) : roleBits ≤ k - quotient k := by
  have hq := quotient_large hk
  have he := quotient_remainder k
  rw [blockSize_eq] at he
  rw [roleBits_eq]
  omega

/-- Every fiber belongs to a complete recursive batch of the actual padded width. -/
theorem complete_batches {k : ℕ} (hk : threshold ≤ k) : width * batchCount k = fiberCount k := by
  rw [width_eq_pow]
  unfold batchCount fiberCount
  rw [← pow_add]
  congr 1
  have h := fiber_exponent_large hk
  omega

theorem batch_partition {k : ℕ} (hk : threshold ≤ k) :
    batchCount k * (width * 2 ^ quotient k) = 2 ^ k := by
  calc
    batchCount k * (width * 2 ^ quotient k) = (width * batchCount k) * 2 ^ quotient k := by ring
    _ = 2 ^ (k - quotient k) * 2 ^ quotient k := by rw [complete_batches hk]; rfl
    _ = 2 ^ k := by
      rw [← pow_add]
      congr 1
      exact Nat.sub_add_cancel (Nat.div_le_self k blockSize)

theorem width_dvd_fibers {k : ℕ} (hk : threshold ≤ k) : width ∣ fiberCount k :=
  ⟨batchCount k, (complete_batches hk).symm⟩

def normalizedCost (T : ℕ → ℝ) (k : ℕ) : ℝ := T k / ((width * 2 ^ k : ℕ) : ℝ)

/-- Exact batching converts the total-cost recurrence into the stated normalized recurrence. -/
theorem normalize_recurrence (T : ℕ → ℝ) (A : ℝ) {k : ℕ} (hk : threshold ≤ k)
    (hstep : T k ≤ A * ((width * 2 ^ k : ℕ) : ℝ) +
      (ExplicitSeedBudget.residuals : ℝ) * (batchCount k : ℝ) * T (quotient k)) :
    normalizedCost T k ≤ A + UniformExponent.lambda * normalizedCost T (quotient k) := by
  have hw : 0 < width := by rw [width_eq_pow]; positivity
  have hv : 0 < ((width * 2 ^ k : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hw (by positivity : 0 < 2 ^ k)
  have hqv : 0 < ((width * 2 ^ quotient k : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hw (by positivity : 0 < 2 ^ quotient k)
  have hb : (batchCount k : ℝ) * ((width * 2 ^ quotient k : ℕ) : ℝ) = ((2 ^ k : ℕ) : ℝ) :=
    by exact_mod_cast batch_partition hk
  have hbv : ((width * 2 ^ k : ℕ) : ℝ) =
      (width : ℝ) * (batchCount k : ℝ) * ((width * 2 ^ quotient k : ℕ) : ℝ) := by
    rw [Nat.cast_mul, ← hb]
    ring
  have hlam : UniformExponent.lambda * (width : ℝ) = (ExplicitSeedBudget.residuals : ℝ) := by
    unfold UniformExponent.lambda width
    have hw0 : (ExplicitSeedBudget.paddedRoles : ℝ) ≠ 0 := by exact_mod_cast hw.ne'
    exact div_mul_cancel₀ _ hw0
  have he : (UniformExponent.lambda *
      (T (quotient k) / ((width * 2 ^ quotient k : ℕ) : ℝ))) * ((width * 2 ^ k : ℕ) : ℝ) =
      (ExplicitSeedBudget.residuals : ℝ) * (batchCount k : ℝ) * T (quotient k) := by
    rw [hbv]
    calc
      _ = (UniformExponent.lambda * (width : ℝ)) * (batchCount k : ℝ) * T (quotient k) := by
        field_simp [hqv.ne']
      _ = _ := by rw [hlam]
  unfold normalizedCost
  apply (div_le_iff₀ hv).2
  rw [add_mul, he]
  exact hstep

/-- Literal arguments obtained by repeatedly taking the paper's quotient. -/
def quotientChain (k j : ℕ) : ℕ := k / blockSize ^ j

theorem quotientChain_zero (k : ℕ) : quotientChain k 0 = k := by simp [quotientChain]

theorem quotientChain_succ (k j : ℕ) : quotientChain k (j + 1) = quotient (quotientChain k j) := by
  simp only [quotientChain, quotient, pow_succ, Nat.div_div_eq_div_mul]

theorem quotientChain_eventually_base (k : ℕ) :
    quotientChain k (Nat.clog blockSize (k + 1)) < threshold := by
  have hpow := Nat.le_pow_clog one_lt_blockSize (k + 1)
  have hk : k < blockSize ^ Nat.clog blockSize (k + 1) := by omega
  have hz : quotientChain k (Nat.clog blockSize (k + 1)) = 0 := Nat.div_eq_of_lt hk
  rw [hz]
  exact threshold_pos

theorem quotientChain_base_exists (k : ℕ) : ∃ j, quotientChain k j < threshold :=
  ⟨Nat.clog blockSize (k + 1), quotientChain_eventually_base k⟩

def depth (k : ℕ) : ℕ := Nat.find (quotientChain_base_exists k)

theorem depth_base (k : ℕ) : quotientChain k (depth k) < threshold :=
  Nat.find_spec (quotientChain_base_exists k)

theorem depth_before_base (k j : ℕ) (hj : j < depth k) : threshold ≤ quotientChain k j := by
  exact Nat.le_of_not_gt (Nat.find_min (quotientChain_base_exists k) hj)

theorem depth_le_clog (k : ℕ) : depth k ≤ Nat.clog blockSize (k + 1) :=
  Nat.find_min' (quotientChain_base_exists k) (quotientChain_eventually_base k)

theorem depth_log_bound (k : ℕ) :
    (depth k : ℝ) ≤ Real.logb UniformExponent.m (k + 1) + 1 := by
  have hn : 0 ≤ Real.logb (blockSize : ℝ) ((k + 1 : ℕ) : ℝ) :=
    Real.logb_nonneg (by exact_mod_cast one_lt_blockSize) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))
  have hc := Nat.ceil_lt_add_one hn
  rw [Real.natCeil_logb_natCast] at hc
  have hd : (depth k : ℝ) ≤ (Nat.clog blockSize (k + 1) : ℝ) := by exact_mod_cast depth_le_clog k
  rw [blockSize_cast] at hc
  simpa only [Nat.cast_add, Nat.cast_one] using hd.trans hc.le

/-- The cost sequence is abstract: the implementation must prove the recurrence and base bound. -/
theorem cost_bound_from_recurrence (t : ℕ → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hstep : ∀ k, threshold ≤ k → t k ≤ A + UniformExponent.lambda * t (quotient k))
    (hbase : ∀ k, k < threshold → t k ≤ B) (k : ℕ) :
    t k ≤ (A / (UniformExponent.lambda - 1) + B) * UniformExponent.lambda *
      (k + 1 : ℝ) ^ UniformExponent.theta := by
  have h := UniformExponent.critical_recurrence_bound A B hA hB
    (fun j => t (quotientChain k j)) (depth k) (k + 1) (by positivity)
    (by
      intro j hj
      rw [quotientChain_succ]
      exact hstep (quotientChain k j) (depth_before_base k j hj))
    (hbase _ (depth_base k)) (depth_log_bound k)
  simpa only [quotientChain_zero] using h

theorem total_cost_bound_from_recurrence (T : ℕ → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hstep : ∀ k, threshold ≤ k → T k ≤ A * ((width * 2 ^ k : ℕ) : ℝ) +
      (ExplicitSeedBudget.residuals : ℝ) * (batchCount k : ℝ) * T (quotient k))
    (hbase : ∀ k, k < threshold → T k ≤ B * ((width * 2 ^ k : ℕ) : ℝ)) (k : ℕ) :
    T k ≤ ((A / (UniformExponent.lambda - 1) + B) * UniformExponent.lambda *
      (k + 1 : ℝ) ^ UniformExponent.theta) * ((width * 2 ^ k : ℕ) : ℝ) := by
  have hw : 0 < width := by rw [width_eq_pow]; positivity
  have hv (j : ℕ) : 0 < ((width * 2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hw (by positivity : 0 < 2 ^ j)
  have h := cost_bound_from_recurrence (normalizedCost T) A B hA hB
    (fun j hj => normalize_recurrence T A hj (hstep j hj))
    (fun j hj => (div_le_iff₀ (hv j)).2 (hbase j hj)) k
  exact (div_le_iff₀ (hv k)).1 h

/-- The final factor of the paper's single supplied root order. -/
def rootBits (L : ℕ) : ℕ := Nat.clog 2 (16 * L)
def rootFactor (L : ℕ) : ℕ := 2 ^ rootBits L
def masterRootOrder (n L : ℕ) : ℕ := (2 * n) * L * rootFactor L

theorem rootBits_ceil (L : ℕ) : rootBits L = ⌈Real.logb 2 ((16 * L : ℕ) : ℝ)⌉₊ :=
  (Real.natCeil_logb_natCast 2 (16 * L)).symm

theorem rootFactor_lower (L : ℕ) : 16 * L ≤ rootFactor L :=
  Nat.le_pow_clog (by norm_num) (16 * L)

theorem rootBits_le {L e : ℕ} (he : 16 * L ≤ 2 ^ e) : rootBits L ≤ e :=
  (Nat.clog_le_iff_le_pow (by norm_num)).2 he

theorem rootFactor_le {L e : ℕ} (he : 16 * L ≤ 2 ^ e) : rootFactor L ≤ 2 ^ e :=
  Nat.pow_le_pow_right (by norm_num) (rootBits_le he)

theorem rootFactor_upper {L : ℕ} (hL : 0 < L) : rootFactor L < 32 * L := by
  have hx : 1 < 16 * L := by omega
  have hc : 0 < rootBits L := Nat.clog_pos (by norm_num) hx
  have hp : 2 ^ (rootBits L - 1) < 16 * L :=
    Nat.pow_pred_clog_lt_self (by norm_num) hx
  have he : rootFactor L = 2 ^ (rootBits L - 1) * 2 := by
    unfold rootFactor
    rw [← pow_succ]
    congr 1
    omega
  rw [he]
  omega

theorem masterRootOrder_bound {n L : ℕ} (hn : 0 < n) (hL : 2 * n ≤ L) (hLn : L < 4 * n) :
    masterRootOrder n L < 1024 * n ^ 3 := by
  have hL0 : 0 < L := by omega
  have hP := rootFactor_upper hL0
  have hsq : L ^ 2 < (4 * n) ^ 2 := Nat.pow_lt_pow_left hLn (by norm_num)
  calc
    masterRootOrder n L < (2 * n) * L * (32 * L) :=
      Nat.mul_lt_mul_of_pos_left hP (by positivity)
    _ = 64 * n * L ^ 2 := by ring
    _ < 64 * n * (4 * n) ^ 2 := Nat.mul_lt_mul_of_pos_left hsq (by positivity)
    _ = 1024 * n ^ 3 := by ring

theorem masterRootOrder_pos {n L : ℕ} (hn : 0 < n) (hL : 0 < L) : 0 < masterRootOrder n L := by
  unfold masterRootOrder rootFactor
  positivity

theorem chirpOrder_dvd (n L : ℕ) : 2 * n ∣ masterRootOrder n L := by
  refine ⟨L * rootFactor L, ?_⟩
  unfold masterRootOrder
  ring

theorem workingOrder_dvd (n L : ℕ) : L ∣ masterRootOrder n L := by
  refine ⟨(2 * n) * rootFactor L, ?_⟩
  unfold masterRootOrder
  ring

theorem rootFactor_dvd (n L : ℕ) : rootFactor L ∣ masterRootOrder n L := by
  refine ⟨(2 * n) * L, ?_⟩
  unfold masterRootOrder
  ring

theorem powerOrder_dvd_factor {L e : ℕ} (he : 2 ^ e ≤ 16 * L) : 2 ^ e ∣ rootFactor L := by
  have h : e ≤ rootBits L :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (he.trans (rootFactor_lower L))
  exact Nat.pow_dvd_pow 2 h

/-- Every power-of-two order needed by a local compiler divides the supplied order. -/
theorem localPowerOrder_dvd {n L r e : ℕ} (hr : r ≤ L) (he : 2 ^ e ≤ 8 * r) :
    2 ^ e ∣ masterRootOrder n L := by
  have h : 2 ^ e ≤ 16 * L := by omega
  exact (powerOrder_dvd_factor h).trans (rootFactor_dvd n L)

end
end ExactFourierCircuits.UniformBatching

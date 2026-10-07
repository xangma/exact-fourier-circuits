import UniformWorkingPreparation

/- A computable charged-count majorant for the paper's recursive schedule.
   No executable scheduler or fixed RAM realization of these charges is asserted. -/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformNetworkCost
open Filter Asymptotics

/-- Reserved absolute construction charge for fixed radix-`2^m` column tables. -/
def tableCharge : ℕ := 128 * (ExplicitSeedBudget.residuals +
    ExplicitSeedBudget.pointwiseCalls + UniformBatching.width + 1) *
    (UniformBatching.blockSize + 1) ^ 3 * 2 ^ UniformBatching.blockSize
/-- Reserved traversal, scalar, movement, terminal, leftover-factor and batch work. -/
def layerUnit : ℕ := 128 * (ExplicitSeedBudget.residuals +
    ExplicitSeedBudget.pointwiseCalls + UniformBatching.width + UniformBatching.blockSize + 1)
def volume (k : ℕ) : ℕ := UniformBatching.width * 2 ^ k

def simultaneousCount (k : ℕ) : ℕ :=
  if hk : k < UniformBatching.threshold then
    (8 * k + 8) * volume k + tableCharge
  else
    layerUnit * volume k + tableCharge +
      ExplicitSeedBudget.residuals * UniformBatching.batchCount k *
        simultaneousCount (UniformBatching.quotient k)
termination_by k
decreasing_by exact UniformBatching.quotient_lt (Nat.le_of_not_gt hk)

def recurrenceUnit : ℕ := layerUnit + tableCharge
def baseUnit : ℕ := 8 * UniformBatching.threshold + 8 + tableCharge

theorem volume_pos (k : ℕ) : 0 < volume k := by
  unfold volume
  rw [UniformBatching.width_eq_pow]
  positivity

theorem simultaneousCount_base {k : ℕ} (hk : k < UniformBatching.threshold) :
    simultaneousCount k = (8 * k + 8) * volume k + tableCharge := by
  rw [simultaneousCount, dite_eq_left hk]

theorem simultaneousCount_step {k : ℕ} (hk : UniformBatching.threshold ≤ k) :
    simultaneousCount k = layerUnit * volume k + tableCharge +
      ExplicitSeedBudget.residuals * UniformBatching.batchCount k *
        simultaneousCount (UniformBatching.quotient k) := by
  rw [simultaneousCount, dite_eq_right (Nat.not_lt.mpr hk)]

theorem simultaneousCount_recurrence {k : ℕ} (hk : UniformBatching.threshold ≤ k) :
    simultaneousCount k ≤ recurrenceUnit * volume k +
      ExplicitSeedBudget.residuals * UniformBatching.batchCount k *
        simultaneousCount (UniformBatching.quotient k) := by
  rw [simultaneousCount_step hk]
  have ht := Nat.mul_le_mul_left tableCharge (show 1 ≤ volume k from volume_pos k)
  unfold recurrenceUnit
  nlinarith

theorem simultaneousCount_base_bound {k : ℕ} (hk : k < UniformBatching.threshold) :
    simultaneousCount k ≤ baseUnit * volume k := by
  rw [simultaneousCount_base hk]
  have ht := Nat.mul_le_mul_left tableCharge (show 1 ≤ volume k from volume_pos k)
  have hm := Nat.mul_le_mul_right (volume k)
    (show 8 * k + 8 ≤ 8 * UniformBatching.threshold + 8 by omega)
  unfold baseUnit
  nlinarith

noncomputable def networkConstant : ℝ :=
  (((recurrenceUnit : ℝ) / (UniformExponent.lambda - 1) + baseUnit) * UniformExponent.lambda)

theorem networkConstant_nonneg : 0 ≤ networkConstant := by
  unfold networkConstant
  exact mul_nonneg (add_nonneg
    (div_nonneg (Nat.cast_nonneg _) (by linarith [UniformExponent.one_lt_lambda]))
    (Nat.cast_nonneg _)) UniformExponent.lambda_pos.le

theorem simultaneousCount_normalized_recurrence {k : ℕ} (hk : UniformBatching.threshold ≤ k) :
    UniformBatching.normalizedCost (fun j => (simultaneousCount j : ℝ)) k ≤
      (recurrenceUnit : ℝ) + UniformExponent.lambda *
        UniformBatching.normalizedCost (fun j => (simultaneousCount j : ℝ)) (UniformBatching.quotient k) := by
  apply UniformBatching.normalize_recurrence _ _ hk
  exact_mod_cast simultaneousCount_recurrence hk

/-- The step/base bounds come from the actual Nat definition, without abstract premises. -/
theorem simultaneousCount_critical_bound (k : ℕ) :
    (simultaneousCount k : ℝ) ≤ networkConstant * (k + 1 : ℝ) ^ UniformExponent.theta * (volume k : ℝ) := by
  exact UniformBatching.total_cost_bound_from_recurrence
    (fun j => (simultaneousCount j : ℝ)) recurrenceUnit baseUnit
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (fun j hj => by exact_mod_cast simultaneousCount_recurrence hj)
    (fun j hj => by exact_mod_cast simultaneousCount_base_bound hj) k

/-- Extra-role zero initialization, input/output movement and a fixed header. -/
def singleCount (k : ℕ) : ℕ := simultaneousCount k + 8 * UniformBatching.width * 2 ^ k + tableCharge
noncomputable def singleConstant : ℝ :=
  networkConstant * (UniformBatching.width : ℝ) + 8 * UniformBatching.width + tableCharge

theorem singleConstant_nonneg : 0 ≤ singleConstant := by
  unfold singleConstant
  exact add_nonneg (add_nonneg (mul_nonneg networkConstant_nonneg (Nat.cast_nonneg _))
    (mul_nonneg (by norm_num) (Nat.cast_nonneg _))) (Nat.cast_nonneg _)

theorem exponentFactor_one_le (k : ℕ) : 1 ≤ (k + 1 : ℝ) ^ UniformExponent.theta :=
  Real.one_le_rpow (by exact_mod_cast Nat.succ_pos k) UniformExponent.theta_pos.le

theorem singleCount_bound (k : ℕ) :
    (singleCount k : ℝ) ≤ singleConstant * (k + 1 : ℝ) ^ UniformExponent.theta * (2 ^ k : ℕ) := by
  have hc := simultaneousCount_critical_bound k
  have hx := exponentFactor_one_le k
  have hp : (1 : ℝ) ≤ (2 ^ k : ℕ) := by exact_mod_cast (show 1 ≤ 2 ^ k by have h : 0 < 2 ^ k := pow_pos (by omega) _; omega)
  have ht : (tableCharge : ℝ) ≤ (tableCharge : ℝ) * (k + 1 : ℝ) ^ UniformExponent.theta * (2 ^ k : ℕ) := by
    have hprod : 1 ≤ (k + 1 : ℝ) ^ UniformExponent.theta * (2 ^ k : ℕ) :=
      calc
        1 = (1 : ℝ) * 1 := by ring
        _ ≤ _ := mul_le_mul hx hp (by linarith) (by linarith)
    simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg tableCharge)
  have hm := mul_le_mul_of_nonneg_right hx
    (show 0 ≤ (8 : ℝ) * UniformBatching.width * (2 ^ k : ℕ) from
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
  unfold volume at hc
  unfold singleCount singleConstant
  push_cast at hc hp ht hm ⊢
  nlinarith

/-- Whole-number per-entry envelope using natural division. -/
def perEntryCount (k : ℕ) : ℕ := singleCount k / 2 ^ k + 1
def perEntryMaximum : ℕ → ℕ
  | 0 => perEntryCount 0
  | k + 1 => max (perEntryMaximum k) (perEntryCount (k + 1))

theorem singleCount_le_perEntry (k : ℕ) : singleCount k ≤ perEntryCount k * 2 ^ k := by
  have he := Nat.div_add_mod (singleCount k) (2 ^ k)
  have hr := Nat.mod_lt (singleCount k) (show 0 < 2 ^ k by positivity)
  unfold perEntryCount
  nlinarith

theorem perEntryCount_le_maximum {k ell : ℕ} (hk : k ≤ ell) : perEntryCount k ≤ perEntryMaximum ell := by
  induction ell with
  | zero =>
    have he : k = 0 := by omega
    simp only [he, perEntryMaximum]
    exact le_rfl
  | succ ell ih =>
    by_cases he : k = ell + 1
    · subst k; exact le_max_right _ _
    · exact (ih (by omega)).trans (le_max_left _ _)

theorem perEntryCount_bound (k : ℕ) :
    (perEntryCount k : ℝ) ≤ (singleConstant + 1) * (k + 1 : ℝ) ^ UniformExponent.theta := by
  have hc := singleCount_bound k
  have hx := exponentFactor_one_le k
  have hd : ((singleCount k / 2 ^ k : ℕ) : ℝ) * (2 ^ k : ℕ) ≤ (singleCount k : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self (singleCount k) (2 ^ k)
  have hp : (0 : ℝ) < (2 ^ k : ℕ) := by exact_mod_cast (show 0 < 2 ^ k by positivity)
  have he : ((singleCount k / 2 ^ k : ℕ) : ℝ) ≤ singleConstant * (k + 1 : ℝ) ^ UniformExponent.theta := by nlinarith
  unfold perEntryCount
  push_cast
  nlinarith

theorem perEntryMaximum_bound (ell : ℕ) :
    (perEntryMaximum ell : ℝ) ≤ (singleConstant + 1) * (ell + 1 : ℝ) ^ UniformExponent.theta := by
  induction ell with
  | zero => exact perEntryCount_bound 0
  | succ ell ih =>
    have hpow := Real.rpow_le_rpow (show 0 ≤ (ell + 1 : ℝ) by positivity)
      (show (ell + 1 : ℝ) ≤ (ell + 1 : ℝ) + 1 by linarith) UniformExponent.theta_pos.le
    have hm := mul_le_mul_of_nonneg_left hpow (by linarith [singleConstant_nonneg] : 0 ≤ singleConstant + 1)
    rw [perEntryMaximum, Nat.cast_max]
    have hpoint := perEntryCount_bound (ell + 1)
    norm_num only [Nat.cast_add, Nat.cast_one] at hpoint ⊢
    exact max_le (ih.trans hm) hpoint

def layerCount (R ell : ℕ) : ℕ := (32 + perEntryMaximum ell) * R

theorem sector_partition_bound (sectors : List ℕ) (ell R : ℕ)
    (haxes : ∀ k ∈ sectors, k ≤ ell) (hwidth : (sectors.map (fun k => 2 ^ k)).sum = R) :
    (sectors.map singleCount).sum + 32 * R ≤ layerCount R ell := by
  have hsum : (sectors.map singleCount).sum ≤ perEntryMaximum ell * (sectors.map (fun k => 2 ^ k)).sum := by
    clear hwidth
    induction sectors with
    | nil => simp
    | cons k ks ih =>
      have hk := haxes k (by simp)
      have hrest : ∀ q ∈ ks, q ≤ ell := fun q hq => haxes q (by simp [hq])
      have hpoint := (singleCount_le_perEntry k).trans
        (Nat.mul_le_mul_right (2 ^ k) (perEntryCount_le_maximum hk))
      have htail := ih hrest
      simp only [List.map_cons, List.sum_cons]
      nlinarith
  rw [hwidth] at hsum
  unfold layerCount
  nlinarith

/-- Reserved common local slot count; realization by the compiler is separate. -/
def slotCount (n : ℕ) : ℕ := 64 * (Nat.clog 2 (UniformWorkingLength.nextPrime n) + 1) ^ 4
noncomputable def axesFactor (n : ℕ) : ℝ :=
  ((UniformWorkingLength.axisCount n + 1 : ℕ) : ℝ) ^ UniformExponent.theta
noncomputable def logFactor (n : ℕ) : ℝ :=
  1 + Real.log ((UniformWorkingLength.axisCount n + 2 : ℕ) : ℝ)

theorem axesFactor_one_le (n : ℕ) : 1 ≤ axesFactor n := by
  simpa only [axesFactor, Nat.cast_add, Nat.cast_one] using
    exponentFactor_one_le (UniformWorkingLength.axisCount n)

theorem logFactor_one_le (n : ℕ) : 1 ≤ logFactor n := by
  have h := Real.log_nonneg
    (show (1 : ℝ) ≤ ((UniformWorkingLength.axisCount n + 2 : ℕ) : ℝ) by exact_mod_cast (show 1 ≤ UniformWorkingLength.axisCount n + 2 by omega))
  unfold logFactor
  linarith

theorem clog_nextPrime_bound (n : ℕ) :
    ((Nat.clog 2 (UniformWorkingLength.nextPrime n) + 1 : ℕ) : ℝ) ≤ 8 * logFactor n := by
  let q := UniformWorkingLength.nextPrime n
  let a := UniformWorkingLength.axisCount n + 2
  have hq3 : 3 ≤ q := by
    have h := UniformWorkingLength.oddPrime_lower (UniformWorkingLength.axisCount n)
    change UniformWorkingLength.axisCount n + 3 ≤ q at h
    omega
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have ha2 : (2 : ℝ) ≤ a := by dsimp [a]; exact_mod_cast (show 2 ≤ UniformWorkingLength.axisCount n + 2 by omega)
  have ha0 : 0 < (a : ℝ) := by linarith
  have hla : 0 ≤ Real.log (a : ℝ) := Real.log_nonneg (by linarith)
  have hq : (q : ℝ) ≤ 64 * (a : ℝ) ^ 2 := by exact_mod_cast UniformWorkingLength.nextPrime_upper n
  have hlog := Real.log_le_log hq0 hq
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  rw [h64] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hnonneg : 0 ≤ Real.logb 2 (q : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ q by omega))
  have hceil := (Nat.ceil_lt_add_one hnonneg).le
  have hceil_eq : ⌈Real.logb 2 (q : ℝ)⌉₊ = Nat.clog 2 q := by
    simpa only [Nat.cast_ofNat] using Real.natCeil_logb_natCast 2 q
  rw [hceil_eq] at hceil
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogb : Real.logb 2 (q : ℝ) ≤ 6 + 4 * Real.log (a : ℝ) := by
    rw [Real.logb, div_le_iff₀ hlog2pos]
    have hm := mul_le_mul_of_nonneg_left UniformWorkingLength.log_two_lower
      (show 0 ≤ 4 * Real.log (a : ℝ) by positivity)
    nlinarith
  have hfinal : (Nat.clog 2 q : ℝ) + 1 ≤ 8 * (1 + Real.log (a : ℝ)) := by linarith
  simpa only [q, a, logFactor, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using hfinal

theorem slotCount_bound (n : ℕ) : (slotCount n : ℝ) ≤ (64 * 8 ^ 4 : ℕ) * logFactor n ^ 4 := by
  have h := clog_nextPrime_bound n
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg _) h 4
  unfold slotCount
  push_cast at hp ⊢
  nlinarith [hp]

theorem binaryExponent_bound {n : ℕ} (hn : 0 < n) :
    ((UniformWorkingLength.doublingExponent n + 1 : ℕ) : ℝ) ≤ 16 * logFactor n := by
  let a := UniformWorkingLength.axisCount n + 2
  let e := UniformWorkingLength.doublingExponent n
  have ha2 : (2 : ℝ) ≤ a := by dsimp [a]; exact_mod_cast (show 2 ≤ UniformWorkingLength.axisCount n + 2 by omega)
  have ha0 : 0 < (a : ℝ) := by linarith
  have hla : 0 ≤ Real.log (a : ℝ) := Real.log_nonneg (by linarith)
  have hB : (2 : ℝ) ^ e ≤ 128 * (a : ℝ) ^ 2 := by
    exact_mod_cast (UniformWorkingLength.binaryFactor_quadratic hn).le
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) e) hB
  rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
  have h128 : Real.log 128 = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
  rw [h128] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hm := mul_le_mul_of_nonneg_left UniformWorkingLength.log_two_lower (Nat.cast_nonneg e)
  have hfinal : (e : ℝ) + 1 ≤ 16 * (1 + Real.log (a : ℝ)) := by
    nlinarith [UniformWorkingLength.log_two_upper]
  simpa only [e, a, logFactor, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using hfinal

def workingCoreCount (n : ℕ) : ℕ :=
  slotCount n * layerCount (UniformWorkingLength.workingLength n) (UniformWorkingLength.axisCount n) +
    8 * UniformWorkingLength.workingLength n * (UniformWorkingLength.doublingExponent n + 1) +
    64 * UniformWorkingLength.workingLength n

/-- `d` is a fixed reserved degree for local compilation/root/table preparation.
    This function does not prove a particular local compiler realizes that reserve. -/
def preparationCount (d n : ℕ) : ℕ :=
  (UniformWorkingPreparation.prepare n).cost + tableCharge * (UniformWorkingLength.axisCount n + 2) ^ d + (tableCharge + 1)
def workingCount (d n : ℕ) : ℕ := workingCoreCount n + preparationCount d n

noncomputable def workingConstant : ℝ :=
  ((64 * 8 ^ 4 : ℕ) : ℝ) * (singleConstant + 33) + 192

theorem workingCost_nonneg (n : ℕ) : 0 ≤ UniformAsymptotics.workingCost UniformExponent.theta n := by
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (le_trans zero_le_one (axesFactor_one_le n)))
    (pow_nonneg (le_trans zero_le_one (logFactor_one_le n)) 4)

theorem workingCoreCount_bound {n : ℕ} (hn : 0 < n) :
    (workingCoreCount n : ℝ) ≤ workingConstant * UniformAsymptotics.workingCost UniformExponent.theta n := by
  let L : ℝ := UniformWorkingLength.workingLength n
  let a := axesFactor n
  let b := logFactor n
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have ha : 1 ≤ a := axesFactor_one_le n
  have hb : 1 ≤ b := logFactor_one_le n
  have hb0 : 0 ≤ b := le_trans zero_le_one hb
  have ha0 : 0 ≤ a := le_trans zero_le_one ha
  have hb4 : b ≤ b ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hb (show 1 ≤ 4 by omega)
  have hpow0 : 0 ≤ b ^ 4 := pow_nonneg hb0 4
  have hmax : (perEntryMaximum (UniformWorkingLength.axisCount n) : ℝ) ≤ (singleConstant + 1) * a := by
    simpa only [a, axesFactor, Nat.cast_add, Nat.cast_one] using
      perEntryMaximum_bound (UniformWorkingLength.axisCount n)
  have hunit : 32 + (perEntryMaximum (UniformWorkingLength.axisCount n) : ℝ) ≤ (singleConstant + 33) * a := by nlinarith
  have hlayer : (layerCount (UniformWorkingLength.workingLength n) (UniformWorkingLength.axisCount n) : ℝ) ≤
      (singleConstant + 33) * a * L := by
    unfold layerCount
    push_cast
    exact mul_le_mul_of_nonneg_right hunit hL
  have hslots : (slotCount n : ℝ) ≤ ((64 * 8 ^ 4 : ℕ) : ℝ) * b ^ 4 := slotCount_bound n
  have hmain : (slotCount n : ℝ) * layerCount (UniformWorkingLength.workingLength n) (UniformWorkingLength.axisCount n) ≤
      ((64 * 8 ^ 4 : ℕ) : ℝ) * (singleConstant + 33) * (L * a * b ^ 4) := by
    calc
      _ ≤ (((64 * 8 ^ 4 : ℕ) : ℝ) * b ^ 4) * ((singleConstant + 33) * a * L) :=
        mul_le_mul hslots hlayer (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hpow0)
      _ = _ := by ring
  have hE : ((UniformWorkingLength.doublingExponent n + 1 : ℕ) : ℝ) ≤ 16 * b := binaryExponent_bound hn
  have hab4 : b ≤ a * b ^ 4 := hb4.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ha hpow0)
  have hbinary : (8 : ℝ) * L * ((UniformWorkingLength.doublingExponent n + 1 : ℕ) : ℝ) ≤
      128 * (L * a * b ^ 4) := by
    calc
      _ ≤ 8 * L * (16 * b) := mul_le_mul_of_nonneg_left hE (mul_nonneg (by norm_num) hL)
      _ = (128 * L) * b := by ring
      _ ≤ (128 * L) * (a * b ^ 4) := mul_le_mul_of_nonneg_left hab4 (mul_nonneg (by norm_num) hL)
      _ = _ := by ring
  have hproduct : 1 ≤ a * b ^ 4 := by
    have hpow : 1 ≤ b ^ 4 := one_le_pow₀ hb
    nlinarith
  have hlinear : (64 : ℝ) * L ≤ 64 * (L * a * b ^ 4) := by
    have h := mul_le_mul_of_nonneg_left hproduct (mul_nonneg (by norm_num : (0 : ℝ) ≤ 64) hL)
    simpa only [mul_one, mul_assoc] using h
  change (workingCoreCount n : ℝ) ≤ workingConstant * (L * a * b ^ 4)
  unfold workingCoreCount workingConstant
  dsimp [L] at hmain hbinary hlinear
  push_cast at hmain hbinary hlinear ⊢
  nlinarith

theorem workingCoreCount_isBigO :
    (fun n : ℕ => (workingCoreCount n : ℝ)) =O[atTop] UniformAsymptotics.workingCost UniformExponent.theta := by
  apply IsBigO.of_bound workingConstant
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (workingCost_nonneg n)]
  exact workingCoreCount_bound (show 0 < n by omega)

theorem input_isBigO_workingCost :
    (fun n : ℕ => (n : ℝ)) =O[atTop] UniformAsymptotics.workingCost UniformExponent.theta := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (workingCost_nonneg n), one_mul]
  have hL : (n : ℝ) ≤ (UniformWorkingLength.workingLength n : ℝ) := by
    have h := UniformWorkingLength.workingLength_lower n
    exact_mod_cast (show n ≤ UniformWorkingLength.workingLength n by omega)
  have ha := axesFactor_one_le n
  have hb : 1 ≤ logFactor n ^ 4 := one_le_pow₀ (logFactor_one_le n)
  have hprod : 1 ≤ axesFactor n * logFactor n ^ 4 := by nlinarith
  have h := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg (UniformWorkingLength.workingLength n) :
    (0 : ℝ) ≤ UniformWorkingLength.workingLength n)
  unfold UniformAsymptotics.workingCost
  change (n : ℝ) ≤ (UniformWorkingLength.workingLength n : ℝ) * axesFactor n * logFactor n ^ 4
  nlinarith

theorem preparationCount_isLittleO_input (d : ℕ) :
    (fun n : ℕ => (preparationCount d n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  have hlog : (fun n : ℕ => Real.log (n : ℝ) ^ d) =o[atTop] (fun n : ℕ => (n : ℝ)) :=
    Real.isLittleO_pow_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hpoly := (UniformWorkingPreparation.axisCount_plus_two_isBigO_log.pow d).trans_isLittleO hlog
  have hlocal := hpoly.const_mul_left (tableCharge : ℝ)
  have hconst : (fun _ : ℕ => ((tableCharge + 1 : ℕ) : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
    simpa only [Function.comp_def, id_eq] using
      (isLittleO_const_id_atTop ((tableCharge + 1 : ℕ) : ℝ)).comp_tendsto tendsto_natCast_atTop_atTop
  simpa only [preparationCount, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one] using
    (UniformWorkingPreparation.preparation_isLittleO_input.add hlocal).add hconst

/-- All cost hypotheses are discharged for this prescribed count function. Scheduler,
    local compiler and fixed-program realization obligations remain independent. -/
theorem workingCount_isBigO_workingCost (d : ℕ) :
    (fun n : ℕ => (workingCount d n : ℝ)) =O[atTop] UniformAsymptotics.workingCost UniformExponent.theta := by
  simpa only [workingCount, Nat.cast_add] using
    workingCoreCount_isBigO.add ((preparationCount_isLittleO_input d).isBigO.trans input_isBigO_workingCost)

theorem workingCount_isBigO_paper (d : ℕ) :
    (fun n : ℕ => (workingCount d n : ℝ)) =O[atTop] UniformMachine.asymptoticCost UniformExponent.theta :=
  (workingCount_isBigO_workingCost d).trans UniformAsymptotics.workingCost_isBigO_paper

theorem workingCount_isLittleO_decimal (d : ℕ) :
    (fun n : ℕ => (workingCount d n : ℝ)) =o[atTop] UniformAsymptotics.decimalCost :=
  (workingCount_isBigO_paper d).trans_isLittleO UniformAsymptotics.paperCost_isLittleO_decimal

end ExactFourierCircuits.UniformNetworkCost

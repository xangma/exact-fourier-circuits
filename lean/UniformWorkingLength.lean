import UniformBatching
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Chebyshev

/- Computable prime/product/doubling selections. No preparation-cost bound is asserted. -/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformWorkingLength

theorem oddPrime_exists (j : ℕ) : ∃ p, Nat.Prime p ∧ Nat.primeCounting' p = j + 1 :=
  ⟨Nat.nth Nat.Prime (j + 1), Nat.prime_nth_prime _, Nat.primeCounting'_nth_eq _⟩

/-- Decidable search; the noncomputable `Nat.nth` appears only in its termination proof. -/
def oddPrime (j : ℕ) : ℕ := Nat.find (oddPrime_exists j)

theorem oddPrime_prime (j : ℕ) : Nat.Prime (oddPrime j) := (Nat.find_spec (oddPrime_exists j)).1
theorem oddPrime_count (j : ℕ) : Nat.primeCounting' (oddPrime j) = j + 1 :=
  (Nat.find_spec (oddPrime_exists j)).2

theorem oddPrime_eq_nth (j : ℕ) : oddPrime j = Nat.nth Nat.Prime (j + 1) := by
  have h := Nat.nth_count (oddPrime_prime j)
  change Nat.nth Nat.Prime (Nat.primeCounting' (oddPrime j)) = oddPrime j at h
  rw [oddPrime_count] at h
  exact h.symm

theorem oddPrime_lower (j : ℕ) : j + 3 ≤ oddPrime j := by
  rw [oddPrime_eq_nth]
  exact Nat.add_two_le_nth_prime (j + 1)

theorem oddPrime_gt_two (j : ℕ) : 2 < oddPrime j := by have h := oddPrime_lower j; omega

theorem oddPrime_odd (j : ℕ) : Odd (oddPrime j) :=
  (oddPrime_prime j).odd_of_ne_two (oddPrime_gt_two j).ne'

theorem oddPrime_strictMono : StrictMono oddPrime := by
  intro i j hij
  simp only [oddPrime_eq_nth]
  exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime) (Nat.add_lt_add_right hij 1)

theorem oddPrime_coprime {i j : ℕ} (hij : i ≠ j) : Nat.Coprime (oddPrime i) (oddPrime j) := by
  exact (oddPrime_prime i).coprime_iff_not_dvd.mpr (by
    intro h
    have he := (oddPrime_prime j).eq_one_or_self_of_dvd (oddPrime i) h
    rcases he with he | he
    · have hp := (oddPrime_prime i).two_le; omega
    · exact hij (oddPrime_strictMono.injective he))

def primeProduct : ℕ → ℕ
  | 0 => 1
  | j + 1 => primeProduct j * oddPrime j

theorem primeProduct_pos (j : ℕ) : 0 < primeProduct j := by
  induction j with
  | zero => simp [primeProduct]
  | succ j ih => exact Nat.mul_pos ih (oddPrime_prime j).pos

theorem primeProduct_odd (j : ℕ) : Odd (primeProduct j) := by
  induction j with
  | zero => simp [primeProduct]
  | succ j ih => exact ih.mul (oddPrime_odd j)

theorem primeProduct_eq_prod (j : ℕ) : primeProduct j = ∏ i ∈ Finset.range j, oddPrime i := by
  induction j with
  | zero => simp [primeProduct]
  | succ j ih => rw [primeProduct, Finset.prod_range_succ, ih]

theorem primeProduct_lower (j : ℕ) : 3 ^ j ≤ primeProduct j := by
  induction j with
  | zero => simp [primeProduct]
  | succ j ih =>
    rw [primeProduct, pow_succ]
    exact Nat.mul_le_mul ih (by have h := oddPrime_lower j; omega)

theorem primeProduct_strictMono : StrictMono primeProduct := by
  apply strictMono_nat_of_lt_succ
  intro j
  have hp := primeProduct_pos j
  have hq := oddPrime_gt_two j
  change primeProduct j < primeProduct j * oddPrime j
  nlinarith

theorem product_exceeds_exists (n : ℕ) : ∃ j, 2 * n < primeProduct j :=
  ⟨2 * n, (Nat.lt_pow_self (by norm_num : 1 < 3)).trans_le (primeProduct_lower (2 * n))⟩

def firstExceed (n : ℕ) : ℕ := Nat.find (product_exceeds_exists n)
def axisCount (n : ℕ) : ℕ := firstExceed n - 1
def oddProduct (n : ℕ) : ℕ := primeProduct (axisCount n)
def nextPrime (n : ℕ) : ℕ := oddPrime (axisCount n)

theorem firstExceed_bound (n : ℕ) : firstExceed n ≤ 2 * n :=
  Nat.find_min' (product_exceeds_exists n)
    ((Nat.lt_pow_self (by norm_num : 1 < 3)).trans_le (primeProduct_lower (2 * n)))

theorem firstExceed_pos {n : ℕ} (hn : 0 < n) : 0 < firstExceed n := by
  have hs := Nat.find_spec (product_exceeds_exists n)
  by_contra h
  have he : firstExceed n = 0 := by omega
  change 2 * n < primeProduct (firstExceed n) at hs
  rw [he, primeProduct] at hs
  omega

theorem maximal_product {n : ℕ} (hn : 0 < n) :
    oddProduct n ≤ 2 * n ∧ 2 * n < oddProduct n * nextPrime n := by
  have hp := firstExceed_pos hn
  have hs := Nat.find_spec (product_exceeds_exists n)
  have hmin := Nat.find_min (product_exceeds_exists n) (show axisCount n < firstExceed n by unfold axisCount; omega)
  constructor
  · exact Nat.le_of_not_gt hmin
  · have he : firstExceed n = axisCount n + 1 := by unfold axisCount; omega
    change 2 * n < primeProduct (firstExceed n) at hs
    rw [he, primeProduct] at hs
    exact hs

theorem oddProduct_pos (n : ℕ) : 0 < oddProduct n := primeProduct_pos _

theorem axisCount_log_bound {n : ℕ} (hn : 0 < n) : axisCount n ≤ Nat.log 3 (2 * n) :=
  Nat.le_log_of_pow_le (by norm_num) ((primeProduct_lower _).trans (maximal_product hn).1)

theorem doubling_exists (n : ℕ) : ∃ e, 2 * n ≤ oddProduct n * 2 ^ e := by
  refine ⟨2 * n, ?_⟩
  have hpow := (Nat.lt_pow_self (by norm_num : 1 < 2) (n := 2 * n)).le
  have hprod := oddProduct_pos n
  nlinarith

def doublingExponent (n : ℕ) : ℕ := Nat.find (doubling_exists n)
def binaryFactor (n : ℕ) : ℕ := 2 ^ doublingExponent n
def workingLength (n : ℕ) : ℕ := oddProduct n * binaryFactor n

theorem workingLength_lower (n : ℕ) : 2 * n ≤ workingLength n := Nat.find_spec (doubling_exists n)

theorem doubling_minimal (n e : ℕ) (he : e < doublingExponent n) : oddProduct n * 2 ^ e < 2 * n :=
  Nat.lt_of_not_ge (Nat.find_min (doubling_exists n) he)

theorem workingLength_upper {n : ℕ} (hn : 0 < n) : workingLength n < 4 * n := by
  by_cases he : doublingExponent n = 0
  · have h := (maximal_product hn).1
    simp only [workingLength, binaryFactor, he, pow_zero, Nat.mul_one]
    omega
  · have hmin := doubling_minimal n (doublingExponent n - 1) (by omega)
    have hpow : 2 ^ doublingExponent n = 2 ^ (doublingExponent n - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    unfold workingLength binaryFactor
    rw [hpow]
    rw [← Nat.mul_assoc]
    omega

theorem binaryFactor_upper {n : ℕ} (hn : 0 < n) : binaryFactor n < 2 * nextPrime n := by
  have hL := workingLength_upper hn
  have hmax := (maximal_product hn).2
  have hR := oddProduct_pos n
  unfold workingLength at hL
  nlinarith

theorem workingLength_pos {n : ℕ} (hn : 0 < n) : 0 < workingLength n := by
  have h := workingLength_lower n
  omega

theorem oddProduct_coprime_binaryFactor (n : ℕ) : Nat.Coprime (oddProduct n) (binaryFactor n) :=
  (Nat.coprime_two_right.mpr (primeProduct_odd _)).pow_right _

theorem selected_masterRoot_bound {n : ℕ} (hn : 0 < n) :
    UniformBatching.masterRootOrder n (workingLength n) < 1024 * n ^ 3 :=
  UniformBatching.masterRootOrder_bound hn (workingLength_lower n) (workingLength_upper hn)

theorem log_two_lower : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ)⁻¹)
  rw [Real.log_inv] at h
  norm_num at h
  linarith

theorem log_two_upper : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ))
  norm_num at h
  exact h

/-- A conservative explicit quadratic count bound from Mathlib's elementary Chebyshev bound. -/
theorem primeCounting_quadratic (j : ℕ) : j + 2 ≤ Nat.primeCounting (64 * (j + 2) ^ 2) := by
  let a : ℕ := j + 2
  let N : ℕ := 64 * a ^ 2
  change a ≤ Nat.primeCounting N
  have ha : 2 ≤ a := by dsimp [a]; omega
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast (show 0 < a by omega)
  have haPow : 0 < a ^ 2 := pow_pos (by omega) _
  have hN : 1 < N := by dsimp [N]; omega
  have hN1 : 1 < (N : ℝ) := by exact_mod_cast hN
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlogN0 : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hNreal : (N : ℝ) = (2 : ℝ) ^ 6 * (a : ℝ) ^ 2 := by dsimp [N]; push_cast; norm_num
  have hlogN : Real.log (N : ℝ) ≤ 2 * (a : ℝ) + 4 := by
    rw [hNreal, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have h := Real.log_le_sub_one_of_pos ha0
    linarith [log_two_upper]
  have hlogN1 : Real.log ((N : ℝ) + 1) ≤ Real.log 2 + Real.log (N : ℝ) := by
    have h := Real.log_le_log (by positivity : 0 < (N : ℝ) + 1)
      (show (N : ℝ) + 1 ≤ 2 * (N : ℝ) by linarith)
    rw [Real.log_mul (by norm_num) hN0.ne'] at h
    exact h
  have hc : (a : ℝ) ≤ ((N : ℝ) * Real.log 2 - Real.log ((N : ℝ) + 1)) / Real.log (N : ℝ) := by
    apply (le_div_iff₀ hlogN0).2
    have har : 2 ≤ (a : ℝ) := by exact_mod_cast ha
    have hNa : (N : ℝ) = 64 * (a : ℝ) ^ 2 := by dsimp [N]; push_cast; rfl
    have hmul : ((a : ℝ) + 1) * Real.log (N : ℝ) ≤ ((a : ℝ) + 1) * (2 * (a : ℝ) + 4) :=
      mul_le_mul_of_nonneg_left hlogN (by positivity)
    have hlow : ((N : ℝ) - 1) * ((1 : ℝ) / 2) ≤ ((N : ℝ) - 1) * Real.log 2 :=
      mul_le_mul_of_nonneg_left log_two_lower (by linarith)
    nlinarith
  have hpi := Chebyshev.pi_ge N
  have hr : (a : ℝ) ≤ (Nat.primeCounting N : ℝ) := hc.trans hpi
  exact_mod_cast hr

theorem oddPrime_upper (j : ℕ) : oddPrime j ≤ 64 * (j + 2) ^ 2 := by
  rw [oddPrime_eq_nth]
  have hp := primeCounting_quadratic j
  have hc : j + 1 < Nat.count Nat.Prime (64 * (j + 2) ^ 2 + 1) := by
    change j + 1 < Nat.primeCounting (64 * (j + 2) ^ 2)
    omega
  have h := Nat.nth_lt_of_lt_count hc
  omega

theorem nextPrime_upper (n : ℕ) : nextPrime n ≤ 64 * (axisCount n + 2) ^ 2 := oddPrime_upper _

theorem binaryFactor_quadratic {n : ℕ} (hn : 0 < n) : binaryFactor n < 128 * (axisCount n + 2) ^ 2 := by
  have hp := nextPrime_upper n
  have h := binaryFactor_upper hn
  omega

/-- Integer-value bounds only; no instruction-count claim about the searches. -/
theorem nextPrime_log_bound {n : ℕ} (hn : 0 < n) :
    nextPrime n ≤ 64 * (Nat.log 3 (2 * n) + 2) ^ 2 := by
  calc
    nextPrime n ≤ 64 * (axisCount n + 2) ^ 2 := nextPrime_upper n
    _ ≤ 64 * (Nat.log 3 (2 * n) + 2) ^ 2 := by
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_left (Nat.add_le_add_right (axisCount_log_bound hn) 2) 2

theorem binaryFactor_log_bound {n : ℕ} (hn : 0 < n) :
    binaryFactor n < 128 * (Nat.log 3 (2 * n) + 2) ^ 2 := by
  have h := binaryFactor_upper hn
  have hp := nextPrime_log_bound hn
  omega

theorem stoppingProduct_bound {n : ℕ} (hn : 0 < n) :
    oddProduct n * nextPrime n ≤ (2 * n) * (64 * (Nat.log 3 (2 * n) + 2) ^ 2) :=
  Nat.mul_le_mul (maximal_product hn).1 (nextPrime_log_bound hn)

theorem doublingExponent_log_bound {n : ℕ} (hn : 0 < n) :
    doublingExponent n ≤ Nat.log 2 (128 * (Nat.log 3 (2 * n) + 2) ^ 2) :=
  Nat.le_log_of_pow_le (by norm_num) (binaryFactor_log_bound hn).le

end ExactFourierCircuits.UniformWorkingLength

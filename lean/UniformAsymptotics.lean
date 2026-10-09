import UniformMachine
import UniformExponent
import UniformWorkingLength
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# The final logarithmic shape and decimal consequence

*An explicit power saving for the exact discrete Fourier transform*, OpenAI
math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, §5.1 Lemma 5.1,
PDF p. 21 (`lem:prime-lengths`), and §5.4, PDF p. 23, proof of Theorem 1.1
and Corollary 1.2 (`thm:main`, `cor:decimal`). These are numerical asymptotic
lemmas. `cost_bound_transfer` must be combined with the final actual-execution
budget; this module does not itself assert a terminating machine run.
-/

/- Numeric asymptotic implications only; no operational algorithm is asserted here. -/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAsymptotics
open Filter Asymptotics
noncomputable section

def realCost (theta x : ℝ) : ℝ :=
  x * (Real.log x) ^ theta * (Real.log (Real.log x)) ^ (4 - theta)

def decimalExponent : ℝ := 1 - 1 / 10 ^ 13
def decimalCost (n : ℕ) : ℝ := (n : ℝ) * (Real.log (n : ℝ)) ^ decimalExponent

theorem paper_exponent_lt_decimal : UniformExponent.theta < decimalExponent := by
  have h := UniformExponent.theta_explicit_gap
  unfold decimalExponent
  linarith

/-- Every strict exponent gap absorbs the entire iterated-logarithm factor. -/
/- §5.4, PDF p. 23: every positive gap in the log exponent absorbs the
entire fixed power of log log n; specialize to beta=1-10^(-13) below. -/
theorem realCost_isLittleO (theta beta : ℝ) (hgap : theta < beta) :
    (realCost theta) =o[atTop] (fun x : ℝ => x * (Real.log x) ^ beta) := by
  have hlog := (isLittleO_log_rpow_rpow_atTop (4 - theta) (sub_pos.mpr hgap)).comp_tendsto
    Real.tendsto_log_atTop
  have h := (isBigO_refl (fun x : ℝ => x * (Real.log x) ^ theta) atTop).mul_isLittleO hlog
  refine h.congr' (Eventually.of_forall (fun _ => rfl)) ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  simp only [Function.comp_apply]
  rw [mul_assoc, ← Real.rpow_add (Real.log_pos hx)]
  congr 2
  ring

theorem asymptoticCost_isLittleO (theta beta : ℝ) (hgap : theta < beta) :
    UniformMachine.asymptoticCost theta =o[atTop]
      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^ beta) := by
  change (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^ theta *
    (Real.log (Real.log (n : ℝ))) ^ (4 - theta)) =o[atTop] _
  simpa only [Function.comp_def, realCost] using
    (realCost_isLittleO theta beta hgap).comp_tendsto tendsto_natCast_atTop_atTop

theorem paperCost_isLittleO_decimal :
    UniformMachine.asymptoticCost UniformExponent.theta =o[atTop] decimalCost :=
  asymptoticCost_isLittleO _ _ paper_exponent_lt_decimal

theorem paperCost_isBigO_decimal :
    UniformMachine.asymptoticCost UniformExponent.theta =O[atTop] decimalCost :=
  paperCost_isLittleO_decimal.isBigO

/- Corollary 1.2, PDF p. 2, proved in §5.4, p. 23: transfer a supplied
paper-shaped budget. Actual finalBudget's Big-O proof is separate. -/
theorem cost_bound_transfer (T : ℕ → ℝ)
    (hT : T =O[atTop] UniformMachine.asymptoticCost UniformExponent.theta) :
    T =o[atTop] decimalCost := hT.trans_isLittleO paperCost_isLittleO_decimal

/-- A clearly conditional transfer from the two working-axis estimates used in the paper. -/
/- §5.2 (5.6), PDF p. 22, followed by §5.4, p. 23: combine L=O(n),
ell=O(log n/log log n) and log ell=O(log log n), retaining theta exactly. -/
theorem shape_transfer (theta : ℝ) (htheta : 0 ≤ theta) (L a b : ℕ → ℝ)
    (hL : L =O[atTop] (fun n : ℕ => (n : ℝ)))
    (ha : a =O[atTop] (fun n : ℕ => Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))))
    (hb : b =O[atTop] (fun n : ℕ => Real.log (Real.log (n : ℝ)))) :
    (fun n => L n * (a n) ^ theta * (b n) ^ 4) =O[atTop] UniformMachine.asymptoticCost theta := by
  have htlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpos : ∀ᶠ n : ℕ in atTop, 1 < Real.log (n : ℝ) := htlog.eventually (eventually_gt_atTop 1)
  have hq : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) :=
    hpos.mono (fun n hn => div_nonneg (by linarith) (Real.log_pos hn).le)
  have h := (hL.mul (ha.rpow htheta hq)).mul (hb.pow 4)
  refine h.congr' (Eventually.of_forall (fun _ => rfl)) ?_
  filter_upwards [hpos] with n hn
  unfold UniformMachine.asymptoticCost
  rw [Real.div_rpow (by linarith) (Real.log_pos hn).le,
    Real.rpow_sub (Real.log_pos hn)]
  rw [show (Real.log (Real.log (n : ℝ))) ^ (4 : ℝ) =
      (Real.log (Real.log (n : ℝ))) ^ (4 : ℕ) from Real.rpow_natCast _ _]
  ring

theorem workingLength_isBigO :
    (fun n : ℕ => (UniformWorkingLength.workingLength n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)) := by
  apply IsBigO.of_bound 4
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact_mod_cast (UniformWorkingLength.workingLength_upper (show 0 < n by omega)).le

def workingCost (theta : ℝ) (n : ℕ) : ℝ :=
  (UniformWorkingLength.workingLength n : ℝ) *
    ((UniformWorkingLength.axisCount n + 1 : ℕ) : ℝ) ^ theta *
    (1 + Real.log ((UniformWorkingLength.axisCount n + 2 : ℕ) : ℝ)) ^ 4

theorem workingCost_transfer
    (haxes : (fun n : ℕ => ((UniformWorkingLength.axisCount n + 1 : ℕ) : ℝ)) =O[atTop]
      (fun n : ℕ => Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))))
    (hlogAxes : (fun n : ℕ => 1 + Real.log ((UniformWorkingLength.axisCount n + 2 : ℕ) : ℝ)) =O[atTop]
      (fun n : ℕ => Real.log (Real.log (n : ℝ)))) :
    workingCost UniformExponent.theta =O[atTop] UniformMachine.asymptoticCost UniformExponent.theta :=
  shape_transfer _ UniformExponent.theta_pos.le _ _ _ workingLength_isBigO haxes hlogAxes

theorem workingCost_decimal_transfer
    (haxes : (fun n : ℕ => ((UniformWorkingLength.axisCount n + 1 : ℕ) : ℝ)) =O[atTop]
      (fun n : ℕ => Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))))
    (hlogAxes : (fun n : ℕ => 1 + Real.log ((UniformWorkingLength.axisCount n + 2 : ℕ) : ℝ)) =O[atTop]
      (fun n : ℕ => Real.log (Real.log (n : ℝ)))) :
    workingCost UniformExponent.theta =o[atTop] decimalCost :=
  (workingCost_transfer haxes hlogAxes).trans_isLittleO paperCost_isLittleO_decimal

theorem axisCount_tendsto : Tendsto UniformWorkingLength.axisCount atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b
  refine ⟨UniformWorkingLength.primeProduct (b + 1), ?_⟩
  intro n hn
  have hn0 : 0 < n := (UniformWorkingLength.primeProduct_pos _).trans_le hn
  by_contra h
  have hab : UniformWorkingLength.axisCount n ≤ b := by omega
  have hp : UniformWorkingLength.oddProduct n * UniformWorkingLength.nextPrime n ≤
      UniformWorkingLength.primeProduct (b + 1) := by
    change UniformWorkingLength.primeProduct (UniformWorkingLength.axisCount n) *
      UniformWorkingLength.oddPrime (UniformWorkingLength.axisCount n) ≤ _
    rw [← UniformWorkingLength.primeProduct]
    exact UniformWorkingLength.primeProduct_strictMono.monotone (Nat.add_le_add_right hab 1)
  have hm := (UniformWorkingLength.maximal_product hn0).2
  omega

theorem primeProduct_factorial (j : ℕ) : j.factorial ≤ UniformWorkingLength.primeProduct j := by
  induction j with
  | zero => simp [UniformWorkingLength.primeProduct]
  | succ j ih =>
    rw [Nat.factorial_succ, UniformWorkingLength.primeProduct]
    calc
      (j + 1) * j.factorial ≤ UniformWorkingLength.oddPrime j * UniformWorkingLength.primeProduct j :=
        Nat.mul_le_mul (by have h := UniformWorkingLength.oddPrime_lower j; omega) ih
      _ = _ := Nat.mul_comm _ _

theorem primeProduct_upper (j : ℕ) :
    UniformWorkingLength.primeProduct j ≤ (64 * (j + 1) ^ 2) ^ j := by
  rw [UniformWorkingLength.primeProduct_eq_prod]
  calc
    (∏ i ∈ Finset.range j, UniformWorkingLength.oddPrime i) ≤ ∏ _i ∈ Finset.range j, 64 * (j + 1) ^ 2 := by
      apply Finset.prod_le_prod
      intro i hi
      have hi' := Finset.mem_range.mp hi
      exact (UniformWorkingLength.oddPrime_upper i).trans
        (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left (by omega) 2))
    _ = _ := by simp

theorem axis_log_bounds {n : ℕ} (hn : 0 < n)
    (hell : 32 ≤ UniformWorkingLength.axisCount n)
    (hln : 1 ≤ Real.log (n : ℝ))
    (hlell : 2 ≤ Real.log (UniformWorkingLength.axisCount n : ℝ)) :
    Real.log (n : ℝ) ≤ 32 * (UniformWorkingLength.axisCount n : ℝ) ^ 2 ∧
    (UniformWorkingLength.axisCount n : ℝ) * Real.log (UniformWorkingLength.axisCount n : ℝ) ≤
      4 * Real.log (n : ℝ) ∧
    Real.log (n : ℝ) ≤ 20 * (UniformWorkingLength.axisCount n : ℝ) *
      Real.log (UniformWorkingLength.axisCount n : ℝ) := by
  let ell : ℕ := UniformWorkingLength.axisCount n
  have hel : 32 ≤ ell := hell
  have helR : 32 ≤ (ell : ℝ) := by exact_mod_cast hel
  have hel0 : 0 < ell := by omega
  have helR0 : 0 < (ell : ℝ) := by exact_mod_cast hel0
  have hnR0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlogel0 : 0 ≤ Real.log (ell : ℝ) := by linarith
  have hlog64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    norm_num
  have hlog2ell : Real.log 2 ≤ Real.log (ell : ℝ) := Real.log_le_log (by norm_num) (by linarith)
  have hlogplus : Real.log ((ell : ℝ) + 2) ≤ 2 * Real.log (ell : ℝ) := by
    have h := Real.log_le_log (by positivity : 0 < (ell : ℝ) + 2)
      (show (ell : ℝ) + 2 ≤ (ell : ℝ) ^ 2 by nlinarith)
    rw [Real.log_pow] at h
    norm_num at h
    exact h
  have hmax : (2 : ℝ) * n < (UniformWorkingLength.primeProduct (ell + 1) : ℝ) := by
    exact_mod_cast (UniformWorkingLength.maximal_product hn).2
  have hupper : (UniformWorkingLength.primeProduct (ell + 1) : ℝ) ≤
      (64 * ((ell : ℝ) + 2) ^ 2) ^ (ell + 1) := by exact_mod_cast primeProduct_upper (ell + 1)
  have hlogmax := Real.log_lt_log (by positivity : 0 < (2 : ℝ) * n) hmax
  have hlogupper := Real.log_le_log
    (by exact_mod_cast UniformWorkingLength.primeProduct_pos (ell + 1)) hupper
  rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlogupper
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hlogupper
  have hs : Real.log 64 + 2 * Real.log ((ell : ℝ) + 2) ≤ 10 * Real.log (ell : ℝ) := by
    rw [hlog64]
    linarith
  have hs0 : 0 ≤ Real.log 64 + 2 * Real.log ((ell : ℝ) + 2) := by
    exact add_nonneg (Real.log_nonneg (by norm_num))
      (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith)))
  have hm := mul_le_mul (show (ell : ℝ) + 1 ≤ 2 * ell by linarith) hs hs0 (by positivity)
  rw [Real.log_mul (by norm_num) hnR0.ne'] at hlogmax
  have hlnel : Real.log (n : ℝ) ≤ 20 * ell * Real.log (ell : ℝ) := by
    nlinarith [UniformWorkingLength.log_two_lower]
  have hlin : Real.log (ell : ℝ) ≤ (ell : ℝ) := Real.log_le_self helR0.le
  have hmLin := mul_le_mul_of_nonneg_left hlin (show 0 ≤ 20 * (ell : ℝ) by positivity)
  have hN : Real.log (n : ℝ) ≤ 32 * (ell : ℝ) ^ 2 := by nlinarith
  have hfac : (ell.factorial : ℝ) ≤ (2 : ℝ) * n := by
    exact_mod_cast (primeProduct_factorial ell).trans (UniformWorkingLength.maximal_product hn).1
  have hlogfac := Real.log_le_log (by exact_mod_cast Nat.factorial_pos ell) hfac
  rw [Real.log_mul (by norm_num) hnR0.ne'] at hlogfac
  have hst := Stirling.le_log_factorial_stirling hel0.ne'
  have hp : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hm2 : 2 * (ell : ℝ) ≤ (ell : ℝ) * Real.log (ell : ℝ) :=
    by simpa only [ell, mul_comm] using mul_le_mul_of_nonneg_left hlell helR0.le
  constructor
  · exact hN
  · constructor
    · nlinarith [UniformWorkingLength.log_two_upper]
    · exact hlnel

theorem axisCount_isBigO :
    (fun n : ℕ => ((UniformWorkingLength.axisCount n + 1 : ℕ) : ℝ)) =O[atTop]
      (fun n : ℕ => Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) := by
  have htell : Tendsto (fun n : ℕ => (UniformWorkingLength.axisCount n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp axisCount_tendsto
  have htlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htloglog : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp htlog
  have htlogell : Tendsto (fun n : ℕ => Real.log (UniformWorkingLength.axisCount n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp htell
  apply IsBigO.of_bound 24
  filter_upwards [eventually_ge_atTop (1 : ℕ), axisCount_tendsto.eventually (eventually_ge_atTop 32),
    htlog.eventually (eventually_ge_atTop 1), htloglog.eventually (eventually_ge_atTop 1),
    htlogell.eventually (eventually_ge_atTop 2)] with n hn hell hln hll hlell
  have hn0 : 0 < n := by omega
  have hb := axis_log_bounds hn0 hell hln hlell
  have helR : (32 : ℝ) ≤ (UniformWorkingLength.axisCount n : ℝ) := by exact_mod_cast hell
  have helR0 : 0 < (UniformWorkingLength.axisCount n : ℝ) := by linarith
  have hll0 : 0 < Real.log (Real.log (n : ℝ)) := by linarith
  have hlogll := Real.log_le_log (by linarith : 0 < Real.log (n : ℝ)) hb.1
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlogll
  norm_num only [Nat.cast_ofNat] at hlogll
  have h32 := Real.log_le_log (by norm_num : (0 : ℝ) < 32) helR
  have hlll : Real.log (Real.log (n : ℝ)) ≤ 3 * Real.log (UniformWorkingLength.axisCount n : ℝ) := by linarith
  have hm := mul_le_mul
    (show (UniformWorkingLength.axisCount n : ℝ) + 1 ≤ 2 * UniformWorkingLength.axisCount n by linarith)
    hlll (by linarith) (by positivity)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (div_nonneg (by linarith) hll0.le)]
  norm_num only [Nat.cast_add, Nat.cast_one]
  rw [← mul_div_assoc, le_div_iff₀ hll0]
  nlinarith [hb.2.1]

theorem logAxes_isBigO :
    (fun n : ℕ => 1 + Real.log ((UniformWorkingLength.axisCount n + 2 : ℕ) : ℝ)) =O[atTop]
      (fun n : ℕ => Real.log (Real.log (n : ℝ))) := by
  have htlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htloglog : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp htlog
  apply IsBigO.of_bound 7
  filter_upwards [eventually_ge_atTop (1 : ℕ), htlog.eventually (eventually_ge_atTop 1),
    htloglog.eventually (eventually_ge_atTop 1)] with n hn hln hll
  have hn0 : 0 < n := by omega
  have hnR0 : 0 < (n : ℝ) := by exact_mod_cast hn0
  have haxis : (UniformWorkingLength.axisCount n : ℝ) ≤ Real.logb 3 ((2 * n : ℕ) : ℝ) :=
    (show (UniformWorkingLength.axisCount n : ℝ) ≤ (Nat.log 3 (2 * n) : ℝ) by
      exact_mod_cast UniformWorkingLength.axisCount_log_bound hn0).trans (Real.natLog_le_logb (2 * n) 3)
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3low : (1 : ℝ) / 2 ≤ Real.log 3 := UniformWorkingLength.log_two_lower.trans
    (Real.log_le_log (by norm_num) (by norm_num))
  have hbase : Real.logb 3 ((2 * n : ℕ) : ℝ) ≤ 2 * (1 + Real.log (n : ℝ)) := by
    rw [Real.logb, div_le_iff₀ hlog3pos, Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num) hnR0.ne']
    have hm := mul_le_mul_of_nonneg_left hlog3low
      (show 0 ≤ 2 * (1 + Real.log (n : ℝ)) by linarith)
    nlinarith [UniformWorkingLength.log_two_upper]
  have hA : ((UniformWorkingLength.axisCount n + 2 : ℕ) : ℝ) ≤ 6 * Real.log (n : ℝ) := by
    have h := haxis.trans hbase
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    linarith
  have hA0 : 0 < ((UniformWorkingLength.axisCount n + 2 : ℕ) : ℝ) := by positivity
  have hlogA := Real.log_le_log hA0 hA
  rw [Real.log_mul (by norm_num) (by linarith : Real.log (n : ℝ) ≠ 0)] at hlogA
  have h6 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
  have hleft0 : 0 ≤ 1 + Real.log ((UniformWorkingLength.axisCount n + 2 : ℕ) : ℝ) :=
    add_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ UniformWorkingLength.axisCount n + 2 by omega)))
  rw [Real.norm_of_nonneg hleft0, Real.norm_of_nonneg (by linarith)]
  linarith

theorem workingCost_isBigO_paper :
    workingCost UniformExponent.theta =O[atTop] UniformMachine.asymptoticCost UniformExponent.theta :=
  workingCost_transfer axisCount_isBigO logAxes_isBigO

theorem workingCost_isLittleO_decimal :
    workingCost UniformExponent.theta =o[atTop] decimalCost :=
  workingCost_decimal_transfer axisCount_isBigO logAxes_isBigO

theorem axisCount_plain_isBigO :
    (fun n : ℕ => (UniformWorkingLength.axisCount n : ℝ)) =O[atTop]
      (fun n : ℕ => Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) := by
  have h : (fun n : ℕ => (UniformWorkingLength.axisCount n : ℝ)) =O[atTop]
      (fun n : ℕ => ((UniformWorkingLength.axisCount n + 1 : ℕ) : ℝ)) := by
    apply IsBigO.of_bound 1
    exact Eventually.of_forall (fun n => by
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      norm_num)
  exact h.trans axisCount_isBigO

theorem axisRatio_isBigO :
    (fun n : ℕ => Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) =O[atTop]
      (fun n : ℕ => (UniformWorkingLength.axisCount n : ℝ)) := by
  obtain ⟨c, hc, hbound⟩ := logAxes_isBigO.exists_pos
  have htell : Tendsto (fun n : ℕ => (UniformWorkingLength.axisCount n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp axisCount_tendsto
  have htlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htloglog : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp htlog
  have htlogell : Tendsto (fun n : ℕ => Real.log (UniformWorkingLength.axisCount n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp htell
  apply IsBigO.of_bound (20 * c)
  filter_upwards [eventually_ge_atTop (1 : ℕ), axisCount_tendsto.eventually (eventually_ge_atTop 32),
    htlog.eventually (eventually_ge_atTop 1), htloglog.eventually (eventually_ge_atTop 1),
    htlogell.eventually (eventually_ge_atTop 2), hbound.bound] with n hn hell hln hll hlell hbnd
  have hn0 : 0 < n := by omega
  have hb := axis_log_bounds hn0 hell hln hlell
  have hel0 : 0 < (UniformWorkingLength.axisCount n : ℝ) := by exact_mod_cast (show 0 < UniformWorkingLength.axisCount n by omega)
  have hll0 : 0 < Real.log (Real.log (n : ℝ)) := by linarith
  have hleft0 : 0 ≤ 1 + Real.log ((UniformWorkingLength.axisCount n + 2 : ℕ) : ℝ) :=
    add_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ UniformWorkingLength.axisCount n + 2 by omega)))
  rw [Real.norm_of_nonneg hleft0, Real.norm_of_nonneg (by linarith)] at hbnd
  have hlogle : Real.log (UniformWorkingLength.axisCount n : ℝ) ≤
      1 + Real.log ((UniformWorkingLength.axisCount n + 2 : ℕ) : ℝ) := by
    have h := Real.log_le_log hel0 (show (UniformWorkingLength.axisCount n : ℝ) ≤
      ((UniformWorkingLength.axisCount n + 2 : ℕ) : ℝ) by norm_num)
    linarith
  have hm := mul_le_mul_of_nonneg_left (hlogle.trans hbnd)
    (show 0 ≤ 20 * (UniformWorkingLength.axisCount n : ℝ) by positivity)
  rw [Real.norm_of_nonneg (div_nonneg (by linarith) hll0.le), Real.norm_of_nonneg (by positivity)]
  rw [div_le_iff₀ hll0]
  nlinarith [hb.2.2]

/-- The actual computably selected axis count has the paper's critical shape. -/
/- Lemma 5.1, PDF p. 21: factorial lower/product upper bounds establish
the actual selected odd-axis count's two-sided logarithmic shape. -/
theorem axisCount_isTheta :
    (fun n : ℕ => (UniformWorkingLength.axisCount n : ℝ)) =Θ[atTop]
      (fun n : ℕ => Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) :=
  ⟨axisCount_plain_isBigO, axisRatio_isBigO⟩

theorem logAxisCount_isBigO :
    (fun n : ℕ => Real.log (UniformWorkingLength.axisCount n : ℝ)) =O[atTop]
      (fun n : ℕ => Real.log (Real.log (n : ℝ))) := by
  have h : (fun n : ℕ => Real.log (UniformWorkingLength.axisCount n : ℝ)) =O[atTop]
      (fun n : ℕ => 1 + Real.log ((UniformWorkingLength.axisCount n + 2 : ℕ) : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards [axisCount_tendsto.eventually (eventually_ge_atTop 1)] with n hn
    have hlog0 : 0 ≤ Real.log (UniformWorkingLength.axisCount n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hn)
    have hleft0 : 0 ≤ 1 + Real.log ((UniformWorkingLength.axisCount n + 2 : ℕ) : ℝ) :=
      add_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ UniformWorkingLength.axisCount n + 2 by omega)))
    have hle := Real.log_le_log (by exact_mod_cast (show 0 < UniformWorkingLength.axisCount n by omega))
      (show (UniformWorkingLength.axisCount n : ℝ) ≤ ((UniformWorkingLength.axisCount n + 2 : ℕ) : ℝ) by norm_num)
    rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hleft0]
    linarith
  exact h.trans logAxes_isBigO

theorem logLog_isBigO_logAxisCount :
    (fun n : ℕ => Real.log (Real.log (n : ℝ))) =O[atTop]
      (fun n : ℕ => Real.log (UniformWorkingLength.axisCount n : ℝ)) := by
  have htell : Tendsto (fun n : ℕ => (UniformWorkingLength.axisCount n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp axisCount_tendsto
  have htlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htloglog : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp htlog
  have htlogell : Tendsto (fun n : ℕ => Real.log (UniformWorkingLength.axisCount n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp htell
  apply IsBigO.of_bound 3
  filter_upwards [eventually_ge_atTop (1 : ℕ), axisCount_tendsto.eventually (eventually_ge_atTop 32),
    htlog.eventually (eventually_ge_atTop 1), htloglog.eventually (eventually_ge_atTop 1),
    htlogell.eventually (eventually_ge_atTop 2)] with n hn hell hln hll hlell
  have hb := axis_log_bounds (show 0 < n by omega) hell hln hlell
  have helR : (32 : ℝ) ≤ (UniformWorkingLength.axisCount n : ℝ) := by exact_mod_cast hell
  have helR0 : 0 < (UniformWorkingLength.axisCount n : ℝ) := by linarith
  have hlogll := Real.log_le_log (by linarith : 0 < Real.log (n : ℝ)) hb.1
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlogll
  norm_num only [Nat.cast_ofNat] at hlogll
  have h32 := Real.log_le_log (by norm_num : (0 : ℝ) < 32) helR
  rw [Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by linarith)]
  linarith

theorem logAxisCount_isTheta :
    (fun n : ℕ => Real.log (UniformWorkingLength.axisCount n : ℝ)) =Θ[atTop]
      (fun n : ℕ => Real.log (Real.log (n : ℝ))) :=
  ⟨logAxisCount_isBigO, logLog_isBigO_logAxisCount⟩

end
end ExactFourierCircuits.UniformAsymptotics

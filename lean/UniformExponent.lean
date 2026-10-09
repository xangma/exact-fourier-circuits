import ExplicitSeedBudget
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Exact recurrence exponent

*An explicit power saving for the exact discrete Fourier transform*, OpenAI
math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`: (1.1), PDF p. 2
(`eq:main-constants`), §2.6, (2.10) and Theorem 2.6, PDF pp. 11–12,
and §5.4, PDF p. 23. This module verifies constants and generic recurrence
estimates; it does not by itself construct an all-length algorithm or prove
the log-log absorption needed for Corollary 1.2.
-/

/- Exact exponent constants from the paper's padded network budget.
   This module proves constants and generic estimates, not an all-length algorithm. -/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformExponent
open scoped BigOperators
noncomputable section

/- (1.1), PDF p. 2, and (2.10), PDF p. 11: residuals=S=W_*m-Delta,
so lambda=S/W_*=m-Delta/W_*. The seed budget stores W_*=2^71 and
Delta=6871402692000000 exactly, rather than the illustrative decimal theta. -/
def m : ℝ := ExplicitSeedBudget.m
def lambda : ℝ := (ExplicitSeedBudget.residuals : ℝ) / (ExplicitSeedBudget.paddedRoles : ℝ)
def theta : ℝ := Real.logb m lambda
def epsilon : ℝ := (ExplicitSeedBudget.margin : ℝ) / (m * (ExplicitSeedBudget.paddedRoles : ℝ))
def eta : ℝ := 2 / 10 ^ 13

theorem m_eq : m = 1000000 := by norm_num [m, ExplicitSeedBudget.m]
theorem m_pos : 0 < m := by rw [m_eq]; norm_num
theorem one_lt_m : 1 < m := by rw [m_eq]; norm_num

theorem lambda_eq_sub : lambda = m -
    (ExplicitSeedBudget.margin : ℝ) / (ExplicitSeedBudget.paddedRoles : ℝ) := by
  have hb : (ExplicitSeedBudget.residuals : ℝ) + (ExplicitSeedBudget.margin : ℝ) =
      (ExplicitSeedBudget.paddedRoles : ℝ) * m := by
    change (ExplicitSeedBudget.residuals : ℝ) + (ExplicitSeedBudget.margin : ℝ) =
      (ExplicitSeedBudget.paddedRoles : ℝ) * (ExplicitSeedBudget.m : ℝ)
    exact_mod_cast ExplicitSeedBudget.residual_balance
  have hw : (ExplicitSeedBudget.paddedRoles : ℝ) ≠ 0 := by norm_num [ExplicitSeedBudget.paddedRoles]
  unfold lambda
  field_simp [hw]
  nlinarith

theorem one_lt_lambda : 1 < lambda := by
  norm_num [lambda, ExplicitSeedBudget.residuals, ExplicitSeedBudget.paddedRoles]

theorem lambda_pos : 0 < lambda := lt_trans zero_lt_one one_lt_lambda

theorem lambda_lt_m : lambda < m := by
  norm_num [lambda, m, ExplicitSeedBudget.residuals, ExplicitSeedBudget.paddedRoles, ExplicitSeedBudget.m]

theorem theta_pos : 0 < theta := Real.logb_pos one_lt_m one_lt_lambda

theorem theta_lt_one : theta < 1 := by
  have h := Real.logb_lt_logb one_lt_m lambda_pos lambda_lt_m
  simpa only [theta, Real.logb_self_eq_one one_lt_m] using h

theorem m_rpow_theta : m ^ theta = lambda :=
  Real.rpow_logb m_pos one_lt_m.ne' lambda_pos

theorem epsilon_exact : epsilon = (1717850673 : ℝ) / 590295810358705651712 := by
  norm_num [epsilon, m, ExplicitSeedBudget.margin, ExplicitSeedBudget.m, ExplicitSeedBudget.paddedRoles]

theorem epsilon_pos : 0 < epsilon := by rw [epsilon_exact]; norm_num
theorem epsilon_lt_one : epsilon < 1 := by rw [epsilon_exact]; norm_num

/- §5.4, PDF p. 23: epsilon>28/10^13 and log m<14 establish the
strict gap theta<1-2/10^13 entirely with exact inequalities. -/
theorem epsilon_lower : (28 : ℝ) / 10 ^ 13 < epsilon := by rw [epsilon_exact]; norm_num

theorem lambda_eq_mul : lambda = m * (1 - epsilon) := by
  rw [lambda_eq_sub]
  unfold epsilon
  field_simp [m_pos.ne']

/-- Seven nonnegative Taylor terms provide this analytic bound using exact rational arithmetic. -/
theorem log_ten_lt : Real.log 10 < (7 : ℝ) / 3 := by
  have hs := Real.sum_le_exp_of_nonneg (x := (7 : ℝ) / 3) (by norm_num) 7
  have hsum : (10 : ℝ) < ∑ i ∈ Finset.range 7, ((7 : ℝ) / 3) ^ i / (Nat.factorial i : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr (hsum.trans_le hs)

theorem log_m_pos : 0 < Real.log m := Real.log_pos one_lt_m

theorem log_m_lt_fourteen : Real.log m < 14 := by
  have hm : m = (10 : ℝ) ^ 6 := by rw [m_eq]; norm_num
  rw [hm, Real.log_pow]
  norm_num
  linarith [log_ten_lt]

theorem eta_pos : 0 < eta := by norm_num [eta]

theorem eta_log_m_lt_epsilon : eta * Real.log m < epsilon := by
  calc
    eta * Real.log m < eta * 14 := mul_lt_mul_of_pos_left log_m_lt_fourteen eta_pos
    _ = (28 : ℝ) / 10 ^ 13 := by norm_num [eta]
    _ < epsilon := epsilon_lower

theorem log_lambda_bound : Real.log lambda ≤ Real.log m - epsilon := by
  have hx : 0 < 1 - epsilon := by linarith [epsilon_lt_one]
  rw [lambda_eq_mul, Real.log_mul m_pos.ne' hx.ne']
  have h := Real.log_le_sub_one_of_pos hx
  linarith

/-- The paper's strict exponent gap is an exact rational inequality. -/
theorem theta_explicit_gap : theta < 1 - (2 : ℝ) / 10 ^ 13 := by
  unfold theta Real.logb
  rw [div_lt_iff₀ log_m_pos]
  have hgap := eta_log_m_lt_epsilon
  unfold eta at hgap
  nlinarith [log_lambda_bound]

theorem theta_decimal_gap : theta < 1 - 2 * (10 : ℝ) ^ (-(13 : ℤ)) := by
  have h := theta_explicit_gap
  norm_num at h ⊢
  exact h

/- Theorem 2.6's unnumbered recurrence unrolling, PDF p. 11: after a
separately supplied finite base bound, sum the affine geometric chain.
The function u, step inequalities and endpoint are premises here; the
machine construction must discharge them before applying this helper. -/
/-- A finite affine recurrence, with its endpoint bound supplied explicitly. -/
theorem affine_chain_bound (l A B : ℝ) (hl : 1 < l) (hA : 0 ≤ A)
    (u : ℕ → ℝ) (d : ℕ)
    (hstep : ∀ j < d, u j ≤ A + l * u (j + 1)) (hend : u d ≤ B) :
    u 0 ≤ (A / (l - 1) + B) * l ^ d := by
  have hl0 : 0 < l := lt_trans zero_lt_one hl
  have hc : A + A / (l - 1) = l * (A / (l - 1)) := by
    field_simp [sub_ne_zero.mpr hl.ne']
    ring
  have hcenter : ∀ d (u : ℕ → ℝ),
      (∀ j < d, u j ≤ A + l * u (j + 1)) →
      u 0 + A / (l - 1) ≤ l ^ d * (u d + A / (l - 1)) := by
    intro d
    induction d with
    | zero => intro u _; simp
    | succ d ih =>
      intro u hs
      have hfirst : u 0 + A / (l - 1) ≤ l * (u 1 + A / (l - 1)) := by
        have h := hs 0 (Nat.zero_lt_succ d)
        norm_num at h
        nlinarith
      have htail := ih (fun j => u (j + 1)) (by
        intro j hj
        exact hs (j + 1) (Nat.succ_lt_succ hj))
      calc
        u 0 + A / (l - 1) ≤ l * (u 1 + A / (l - 1)) := hfirst
        _ ≤ l * (l ^ d * (u (d + 1) + A / (l - 1))) :=
          mul_le_mul_of_nonneg_left htail hl0.le
        _ = l ^ (d + 1) * (u (d + 1) + A / (l - 1)) := by rw [pow_succ]; ring
  have h := hcenter d u hstep
  have hp : 0 ≤ l ^ d := pow_nonneg hl0.le d
  have he := mul_le_mul_of_nonneg_left (add_le_add_right hend (A / (l - 1))) hp
  have hc0 : 0 ≤ A / (l - 1) := div_nonneg hA (by linarith)
  nlinarith

theorem lambda_rpow_logb (x : ℝ) (hx : 0 < x) : lambda ^ Real.logb m x = x ^ theta := by
  calc
    lambda ^ Real.logb m x = (m ^ theta) ^ Real.logb m x := by rw [m_rpow_theta]
    _ = m ^ (theta * Real.logb m x) := (Real.rpow_mul m_pos.le _ _).symm
    _ = m ^ (Real.logb m x * theta) := by rw [mul_comm theta]
    _ = (m ^ Real.logb m x) ^ theta := Real.rpow_mul m_pos.le _ _
    _ = x ^ theta := by rw [Real.rpow_logb m_pos one_lt_m.ne' hx]

/- Theorem 2.6, PDF pp. 11–12: d≤ceil(log_m(k+1)) yields
lambda^d≤lambda*(k+1)^theta. The abstract x below will be k+1;
the caller supplies the actual quotient-chain depth estimate. -/
/-- The supplied logarithmic recursion-depth bound gives the critical exponent, without loss. -/
theorem critical_depth_bound (d : ℕ) (x : ℝ) (hx : 0 < x)
    (hd : (d : ℝ) ≤ Real.logb m x + 1) :
    lambda ^ d ≤ lambda * x ^ theta := by
  calc
    lambda ^ d = lambda ^ (d : ℝ) := (Real.rpow_natCast lambda d).symm
    _ ≤ lambda ^ (Real.logb m x + 1) :=
      Real.rpow_le_rpow_of_exponent_le one_lt_lambda.le hd
    _ = lambda * x ^ theta := by
      rw [Real.rpow_add lambda_pos, Real.rpow_one, lambda_rpow_logb x hx, mul_comm]

/-- Generic recurrence estimate. The algorithm must establish `hstep`, `hend`, and `hd`. -/
theorem critical_recurrence_bound (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (u : ℕ → ℝ) (d : ℕ) (x : ℝ) (hx : 0 < x)
    (hstep : ∀ j < d, u j ≤ A + lambda * u (j + 1)) (hend : u d ≤ B)
    (hd : (d : ℝ) ≤ Real.logb m x + 1) :
    u 0 ≤ (A / (lambda - 1) + B) * lambda * x ^ theta := by
  have hc : 0 ≤ A / (lambda - 1) + B :=
    add_nonneg (div_nonneg hA (by linarith [one_lt_lambda])) hB
  calc
    u 0 ≤ (A / (lambda - 1) + B) * lambda ^ d :=
      affine_chain_bound lambda A B one_lt_lambda hA u d hstep hend
    _ ≤ (A / (lambda - 1) + B) * (lambda * x ^ theta) :=
      mul_le_mul_of_nonneg_left (critical_depth_bound d x hx hd) hc
    _ = (A / (lambda - 1) + B) * lambda * x ^ theta := by ring

end
end ExactFourierCircuits.UniformExponent

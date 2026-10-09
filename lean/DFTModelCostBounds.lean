import OAI.Computability.FourierTransform.Goal
import UniformAsymptotics
import UniformFinalLinearTableCost
import UniformActualGlobalConstants

set_option autoImplicit false

/-! Cost transport only. These theorems do not construct a program compiler or
assume a real-valued clock in either machine. All runtime allowances are Nat. -/
namespace ExactFourierCircuits.DFTModelCost
open Filter Asymptotics
noncomputable section

local notation "sourceCost" => UniformFinalLinearTableCost.finalBudget
  UniformActualGlobalConstants.constants UniformRecursiveSelfCallMachine.W
local notation "paperCost" => UniformMachine.asymptoticCost UniformExponent.theta

/-- The displayed paper exponent is identical in the two contracts. -/
theorem theta_eq : OAI.PowerSaving.theta = UniformExponent.theta := by
  unfold OAI.PowerSaving.theta UniformExponent.theta Real.logb
  rw [UniformExponent.lambda_eq_sub,UniformExponent.m_eq]
  norm_num [OAI.PowerSaving.paperMultiplier,OAI.PowerSaving.paperM,
    OAI.PowerSaving.paperDelta,OAI.PowerSaving.paperW,
    ExplicitSeedBudget.margin,ExplicitSeedBudget.paddedRoles]

theorem paperTime_eq : OAI.PowerSaving.paperTime = paperCost := by
  funext n
  unfold OAI.PowerSaving.paperTime UniformMachine.asymptoticCost
  rw [theta_eq]

theorem decimalTime_eq : OAI.PowerSaving.decimalTime = UniformAsymptotics.decimalCost := rfl

/-- Input/output marshalling and a constant startup allowance are absorbed by
this same paper asymptotic, without changing its exponent. -/
theorem linear_isBigO_paper :
    (fun n : ℕ => (n : ℝ)+1) =O[atTop] paperCost := by
  have one : (fun _n : ℕ => (1 : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)) :=
    ((isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto tendsto_natCast_atTop_atTop).isBigO
  exact ((isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).add one).trans
    UniformFinalOuterCost.input_isBigO_paper

/-- A positive-length bound on a natural operational allowance is sufficient;
its finitely many excluded small inputs have no asymptotic effect. -/
theorem transfer (W : ℕ → ℕ) (C : ℕ)
    (majorant : ∀ n, 0<n → (W n : ℝ) ≤ (C : ℝ)*sourceCost n+(C : ℝ)*((n : ℝ)+1)) :
    (fun n => (W n : ℝ)) =O[atTop] paperCost := by
  have cost := (UniformFinalLinearTableCost.finalBudget_isBigO_paper
    UniformActualGlobalConstants.constants UniformRecursiveSelfCallMachine.W).const_mul_left (C : ℝ)
  have overhead := linear_isBigO_paper.const_mul_left (C : ℝ)
  refine (IsBigO.of_norm_eventuallyLE ?_).trans (cost.add overhead)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have h := majorant n (by omega)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact h

theorem paper_isLittleO_nlogn : paperCost =o[atTop] OAI.PowerSaving.nlogn := by
  change paperCost =o[atTop] (fun n : ℕ => (n : ℝ)*Real.log (n : ℝ))
  simpa only [Real.rpow_one] using
    UniformAsymptotics.asymptoticCost_isLittleO UniformExponent.theta 1
      UniformExponent.theta_lt_one

/-- All three upstream asymptotic conclusions follow from the same charged
paper bound, including its decimal saving and little-o corollary. -/
theorem timeBounds (W : ℕ → ℕ)
    (cost : (fun n => (W n : ℝ)) =O[atTop] paperCost) : OAI.PowerSaving.TimeBounds W := by
  refine ⟨?_,?_,cost.trans_isLittleO paper_isLittleO_nlogn⟩
  · simpa only [paperTime_eq] using cost
  · simpa only [decimalTime_eq] using cost.trans UniformAsymptotics.paperCost_isBigO_decimal

theorem transfer_timeBounds (W : ℕ → ℕ) (C : ℕ)
    (majorant : ∀ n, 0<n → (W n : ℝ) ≤ (C : ℝ)*sourceCost n+(C : ℝ)*((n : ℝ)+1)) :
    OAI.PowerSaving.TimeBounds W := timeBounds W (transfer W C majorant)

/-- A loose polynomial work envelope is sufficient for upstream's address
accounting; this estimate does not serve as an algorithmic stopping clock. -/
theorem paper_isBigO_square :
    paperCost =O[atTop] (fun n : ℕ => (n : ℝ)^2) := by
  have logs : OAI.PowerSaving.nlogn =O[atTop] (fun n : ℕ => (n : ℝ)^2) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog := Real.log_le_self (show 0 ≤ (n : ℝ) by positivity)
    have hnonneg : 0 ≤ OAI.PowerSaving.nlogn n :=
      mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hnR)
    rw [Real.norm_of_nonneg hnonneg,Real.norm_of_nonneg (sq_nonneg _),one_mul]
    unfold OAI.PowerSaving.nlogn
    nlinarith
  exact paper_isLittleO_nlogn.isBigO.trans logs

/-- Convert an actual natural work function with a quadratic Big-O bound to
one global polynomial bound at every positive length. Finite exceptions are
absorbed by a constant, not by a real-valued runtime oracle. -/
theorem work_polynomial (W : ℕ → ℕ)
    (cost : (fun n => (W n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^2)) :
    ∃ degree : ℕ, ∀ n, 0<n → W n+10*(n+2) ≤ (n+2)^degree := by
  obtain ⟨c,large⟩ := cost.bound
  obtain ⟨N,hN⟩ := eventually_atTop.mp large
  let a := Nat.ceil |c|
  let finite := ∑ i ∈ Finset.range N, W i
  let C := a+finite+10
  have ca : c ≤ (a : ℝ) := (le_abs_self c).trans (Nat.le_ceil _)
  have all : ∀ n, W n ≤ C*(n+2)^2 := by
    intro n
    by_cases hn : N ≤ n
    · have h := hN n hn
      rw [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (sq_nonneg _)] at h
      have hc : (a : ℝ) ≤ C := by exact_mod_cast (show a ≤ C by dsimp [C];omega)
      have final : (W n : ℝ) ≤ (C : ℝ)*((n : ℝ)+2)^2 := by
        calc
          (W n : ℝ) ≤ c*(n : ℝ)^2 := h
          _ ≤ (C : ℝ)*(n : ℝ)^2 := mul_le_mul_of_nonneg_right (ca.trans hc) (sq_nonneg _)
          _ ≤ (C : ℝ)*((n : ℝ)+2)^2 := by
            apply mul_le_mul_of_nonneg_left _ (show (0 : ℝ) ≤ (C : ℝ) from Nat.cast_nonneg C)
            nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
      exact_mod_cast final
    · have hf : W n ≤ finite := by
        exact Finset.single_le_sum (fun i _ => Nat.zero_le (W i))
          (Finset.mem_range.mpr (show n<N by omega))
      have fc : finite ≤ C := by dsimp [C];omega
      have one : 1 ≤ (n+2)^2 := Nat.one_le_pow _ _ (by omega)
      exact hf.trans (fc.trans (Nat.le_mul_of_pos_right _ one))
  refine ⟨2*(C+10)+2,fun n hn => ?_⟩
  have square : n+2 ≤ (n+2)^2 := by nlinarith
  have before : W n+10*(n+2) ≤ (C+10)*(n+2)^2+(C+10) := by
    have w := all n
    nlinarith
  exact before.trans (UniformGlobalEnvelope.polynomial_envelope (C+10) 2 n hn)

end
end ExactFourierCircuits.DFTModelCost

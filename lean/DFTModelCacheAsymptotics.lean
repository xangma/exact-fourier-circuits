import DFTModelCacheAllAxisForestsBounds
import DFTModelInitialPreparationBounds

set_option autoImplicit false

/-! The existing closed all-axis spectrum producer has sublinear preparation
work. This concerns its actual charged budget, including the binary CRT axis;
it does not assert a complete typed DFT compiler. -/
namespace ExactFourierCircuits.DFTModelCacheAsymptotics
open Filter Asymptotics
open scoped BigOperators
noncomputable section

def scale (n : ℕ) : ℕ :=
  UniformWorkingLength.axisCount n+2+UniformRootTableMachine.rowBudget n

theorem scale_pos (n : ℕ) : 0 < scale n := by unfold scale; omega

theorem scale_isBigO_log :
    (fun n : ℕ => (scale n : ℝ)) =O[atTop] (fun n : ℕ => Real.log (n : ℝ)) := by
  simpa only [scale,Nat.cast_add] using
    UniformWorkingPreparation.axisCount_plus_two_isBigO_log.add
      UniformRootTableMachine.rowBudget_isBigO_log

theorem monomial_isLittleO_input (c d : ℕ) :
    (fun n : ℕ => ((c*scale n^d : ℕ) : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  have h := (scale_isBigO_log.pow d).const_mul_left (c : ℝ)
  have tail : (fun n : ℕ => Real.log (n : ℝ)^d) =o[atTop] (fun n : ℕ => (n : ℝ)) :=
    Real.isLittleO_pow_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  simpa only [Nat.cast_mul,Nat.cast_pow] using h.trans_isLittleO tail

theorem selected_radix_bound {n : ℕ} (hn : 0 < n)
    (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) :
    UniformAllAxisSeedPreparation.radix n j ≤ 128*scale n^2 := by
  have h := UniformSelectedCRT.radix_quadratic hn j
  exact h.trans (Nat.mul_le_mul_left 128
    (Nat.pow_le_pow_left (by unfold scale; omega) 2))

def forestEnvelope (t : ℕ) : ℕ :=
  100000*(129*t^2)^5+(128*t^2)^2*(100100*(129*t^2)^2+80*t+30)+19

theorem forest_budget_bound {n : ℕ} (hn : 0 < n)
    (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) :
    DFTModelCacheSpectrumForest.workBudget (UniformAllAxisSeedPreparation.radix n j)
      (UniformMasterRootMachine.order n) ≤ forestEnvelope (scale n) := by
  have hr := selected_radix_bound hn j
  have ht := scale_pos n
  have hpow : 1 ≤ scale n^2 := Nat.one_le_pow _ _ ht
  have hr1 : UniformAllAxisSeedPreparation.radix n j+1 ≤ 129*scale n^2 := by omega
  have hl : Nat.log2 (UniformMasterRootMachine.order n+1)+1 ≤ scale n := by
    unfold scale UniformRootTableMachine.rowBudget; omega
  unfold DFTModelCacheSpectrumForest.workBudget
    DFTModelCacheRectanglePreparation.rowBudget forestEnvelope
  gcongr

theorem axis_budgets_bound {n : ℕ} (hn : 0 < n) :
    DFTModelCacheAllAxisForests.axisBudgets n ≤ scale n*forestEnvelope (scale n) := by
  rw [DFTModelCacheAllAxisForests.axisBudgets_eq]
  calc
    _ ≤ ∑ _j : Fin (UniformAllAxisSeedPreparation.axisCount n), forestEnvelope (scale n) :=
      Finset.sum_le_sum (fun j _ => forest_budget_bound hn j)
    _ = UniformAllAxisSeedPreparation.axisCount n*forestEnvelope (scale n) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (by
      change UniformWorkingLength.axisCount n+1 ≤ scale n
      unfold scale; omega)

theorem forest_sum_isLittleO_input :
    (fun n : ℕ => ((scale n*forestEnvelope (scale n) : ℕ) : ℝ))
      =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  have h := ((((monomial_isLittleO_input (100000*129^5) 11).add
    (monomial_isLittleO_input (128^2*100100*129^2) 9)).add
    (monomial_isLittleO_input (128^2*80) 6)).add
    (monomial_isLittleO_input (128^2*30) 5)).add
    (monomial_isLittleO_input 19 1)
  convert h using 1
  ext n
  simp only [forestEnvelope,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring

def allAxisEnvelope (n : ℕ) : ℕ :=
  16*UniformWorkingCompletion.preparationBudget n+
  12*UniformMasterRootMachine.preparationBudget n+32+20*scale n+
  scale n*(40*scale n+82)+scale n*forestEnvelope (scale n)

theorem all_axis_budget_bound {n : ℕ} (hn : 0 < n) :
    DFTModelCacheAllAxisForests.workBudget n ≤ allAxisEnvelope n := by
  have hb := axis_budgets_bound hn
  have ha : UniformWorkingLength.axisCount n+1 ≤ scale n := by unfold scale; omega
  have hl : Nat.log2 (UniformMasterRootMachine.order n+1)+1 ≤ scale n := by
    unfold scale UniformRootTableMachine.rowBudget; omega
  have hm := Nat.mul_le_mul ha (Nat.add_le_add_right (Nat.mul_le_mul_left 40 hl) 82)
  unfold DFTModelCacheAllAxisForests.workBudget DFTModelCacheAxisRoots.budget allAxisEnvelope
  change _+6*UniformMasterRootMachine.preparationBudget n+14+
    20*(UniformWorkingLength.axisCount n+1)+_ ≤ _
  omega

theorem all_axis_envelope_isLittleO_input :
    (fun n : ℕ => (allAxisEnvelope n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  have hp := ((UniformWorkingCompletion.preparationBudget_isLittleO_input.const_mul_left (16 : ℝ)).add
    (UniformMasterRootMachine.preparationBudget_isLittleO_input.const_mul_left (12 : ℝ)))
  have h := (((((hp.add (monomial_isLittleO_input 32 0)).add
    (monomial_isLittleO_input 20 1)).add (monomial_isLittleO_input 40 2)).add
    (monomial_isLittleO_input 82 1)).add forest_sum_isLittleO_input)
  convert h using 1
  ext n
  simp only [allAxisEnvelope,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring

theorem all_axis_budget_isLittleO_input :
    (fun n : ℕ => (DFTModelCacheAllAxisForests.workBudget n : ℝ))
      =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  refine (IsBigO.of_norm_eventuallyLE ?_).trans_isLittleO all_axis_envelope_isLittleO_input
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  simp only [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast all_axis_budget_bound (show 0 < n by omega)

theorem all_axis_budget_isBigO_input :
    (fun n : ℕ => (DFTModelCacheAllAxisForests.workBudget n : ℝ))
      =O[atTop] (fun n : ℕ => (n : ℝ)) := all_axis_budget_isLittleO_input.isBigO

theorem all_axis_work_isLittleO_input :
    (fun n : ℕ => ((OAI.PowerSaving.RAM.run DFTModelCacheAllAxisForests.program
      (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).work : ℝ))
      =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  refine (IsBigO.of_norm_eventuallyLE ?_).trans_isLittleO all_axis_budget_isLittleO_input
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  simp only [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast DFTModelCacheAllAxisForests.program_work n (show 0 < n by omega)

end
end ExactFourierCircuits.DFTModelCacheAsymptotics

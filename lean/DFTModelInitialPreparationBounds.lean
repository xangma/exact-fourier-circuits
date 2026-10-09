import DFTModelInitialPreparation

set_option autoImplicit false

/-! The actual closed initial producer has linear work. Its finite integer
selection budgets and charged power extractions are included in this bound. -/
namespace ExactFourierCircuits.DFTModelInitialPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open Filter Asymptotics
noncomputable section

theorem divided_power_le_rowBudget (n d : ℕ) :
    UniformPowerMachine.loopCost (UniformMasterRootMachine.order n/d)≤
      UniformRootTableMachine.rowBudget n := by
  have he := Nat.div_le_self (UniformMasterRootMachine.order n) d
  have hE : UniformMasterRootMachine.order n/d+1≠0 := Nat.succ_ne_zero _
  have hD : UniformMasterRootMachine.order n+1≠0 := Nat.succ_ne_zero _
  have hp := Nat.log2_self_le hE
  have hm : Nat.log2 (UniformMasterRootMachine.order n/d+1)≤
      Nat.log2 (UniformMasterRootMachine.order n+1) :=
    (Nat.le_log2 hD).2 (hp.trans (Nat.add_le_add_right he 1))
  have hc := UniformPowerMachine.totalCost_log_bound (UniformMasterRootMachine.order n/d)
  unfold UniformRootTableMachine.rowBudget
  omega

theorem budget_le_linear_envelope {n : ℕ} (hn : 0<n) :
    budget n≤38*UniformWorkingCompletion.preparationBudget n+
      12*UniformMasterRootMachine.preparationBudget n+
      440*UniformRootTableMachine.rowBudget n+10000*(n+1) := by
  have h4 := divided_power_le_rowBudget n 4
  have h2 := divided_power_le_rowBudget n (2*n)
  have hL := UniformWorkingLength.workingLength_upper hn
  unfold budget DFTModelOuterPreparation.operandBudget DFTModelOuterPreparation.budget
    UniformCRTTraversalCycle.len
  omega

theorem budget_isBigO_input :
    (fun n : ℕ => (budget n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)) := by
  have hworking := UniformWorkingCompletion.preparationBudget_isLittleO_input.isBigO
  have hmaster := UniformMasterRootMachine.preparationBudget_isLittleO_input.isBigO
  have hlog : (fun n : ℕ => Real.log (n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hrow := UniformRootTableMachine.rowBudget_isBigO_log.trans_isLittleO hlog
  have hone : (fun _n : ℕ => (1 : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)) :=
    ((isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto tendsto_natCast_atTop_atTop).isBigO
  have hlinear := (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).add hone
  have henvelope := (((hworking.const_mul_left (38 : ℝ)).add
    (hmaster.const_mul_left (12 : ℝ))).add (hrow.isBigO.const_mul_left (440 : ℝ))).add
      (hlinear.const_mul_left (10000 : ℝ))
  refine (IsBigO.of_norm_eventuallyLE ?_).trans henvelope
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast budget_le_linear_envelope (show 0<n by omega)

/-- Uniform over any actual input family: the closed producer's measured Bill
work is O(n), with no supplied cost, execution or coefficient premise. -/
theorem work_isBigO_input (x : ∀n : ℕ,Fin n→ℂ) :
    (fun n : ℕ => ((run program
      ((n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)),Tape.mk n (x n))).work : ℝ))
      =O[atTop] (fun n : ℕ => (n : ℝ)) := by
  refine (IsBigO.of_norm_eventuallyLE ?_).trans budget_isBigO_input
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (specification (show 0<n by omega) (x n)).2.2.1

end
end ExactFourierCircuits.DFTModelInitialPreparation

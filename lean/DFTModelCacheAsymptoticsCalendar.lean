import DFTModelCacheAsymptotics
import DFTModelCacheCalendarBounds

set_option autoImplicit false

/-! Summing the genuine per-axis timestamp-constructor budgets over all selected
CRT axes is sublinear. This is the startup construction of the event calendar,
not the later execution of every global clock. -/
namespace ExactFourierCircuits.DFTModelCacheAsymptotics
open Filter Asymptotics
open scoped BigOperators
noncomputable section

def calendarBudget (n : ℕ) : ℕ :=
  ∑ j : Fin (UniformAllAxisSeedPreparation.axisCount n),
    DFTModelCacheCalendar.workBudget (UniformAllAxisSeedPreparation.radix n j)

def calendarEnvelope (t : ℕ) : ℕ := t*DFTModelCacheCalendar.workBudget (128*t^2)

theorem calendar_workBudget_mono {r s : ℕ} (h : r ≤ s) :
    DFTModelCacheCalendar.workBudget r ≤ DFTModelCacheCalendar.workBudget s := by
  unfold DFTModelCacheCalendar.workBudget DFTModelCacheCalendar.localWorkBudget
    DFTModelCacheCalendar.sequenceBudget DFTModelCacheCalendar.eventBudget
  gcongr

theorem calendar_budget_bound {n : ℕ} (hn : 0 < n) :
    calendarBudget n ≤ calendarEnvelope (scale n) := by
  calc
    _ ≤ ∑ _j : Fin (UniformAllAxisSeedPreparation.axisCount n),
        DFTModelCacheCalendar.workBudget (128*scale n^2) :=
      Finset.sum_le_sum (fun j _ => calendar_workBudget_mono (selected_radix_bound hn j))
    _ = UniformAllAxisSeedPreparation.axisCount n*
        DFTModelCacheCalendar.workBudget (128*scale n^2) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (by
      change UniformWorkingLength.axisCount n+1 ≤ scale n
      unfold scale; omega)

theorem calendar_envelope_isLittleO_input :
    (fun n : ℕ => (calendarEnvelope (scale n) : ℝ))
      =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  have h := ((((((monomial_isLittleO_input (4000*128^6) 13).add
    (monomial_isLittleO_input (12034*128^5) 11)).add
    (monomial_isLittleO_input (41017*128^4) 9)).add
    (monomial_isLittleO_input (68384*128^3) 7)).add
    (monomial_isLittleO_input (57656*128^2) 5)).add
    (monomial_isLittleO_input (25498*128) 3)).add
    (monomial_isLittleO_input 4642 1)
  convert h using 1
  ext n
  simp only [calendarEnvelope,DFTModelCacheCalendar.workBudget,
    DFTModelCacheCalendar.localWorkBudget,DFTModelCacheCalendar.sequenceBudget,
    DFTModelCacheCalendar.eventBudget,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring

theorem calendar_budget_isLittleO_input :
    (fun n : ℕ => (calendarBudget n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  refine (IsBigO.of_norm_eventuallyLE ?_).trans_isLittleO calendar_envelope_isLittleO_input
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  simp only [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast calendar_budget_bound (show 0 < n by omega)

theorem calendar_budget_isBigO_input :
    (fun n : ℕ => (calendarBudget n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)) :=
  calendar_budget_isLittleO_input.isBigO

/-- This is the measured charged work of each existing closed calendar Code,
with arbitrary runtime offsets and starting clocks. Neither affects the bound. -/
theorem calendar_work_isLittleO_input
    (offset start : ∀ n : ℕ, Fin (UniformAllAxisSeedPreparation.axisCount n) → ℕ) :
    (fun n : ℕ => ((∑ j : Fin (UniformAllAxisSeedPreparation.axisCount n),
      (OAI.PowerSaving.RAM.run DFTModelCacheCalendar.program
        (UniformAllAxisSeedPreparation.radix n j,(offset n j,start n j))).work : ℕ) : ℝ))
      =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  refine (IsBigO.of_norm_eventuallyLE ?_).trans_isLittleO calendar_budget_isLittleO_input
  filter_upwards [] with n
  simp only [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (Finset.sum_le_sum (fun j _ => DFTModelCacheCalendar.program_work
    (UniformAllAxisSeedPreparation.radix n j) (offset n j) (start n j)))

theorem preparation_and_cache_isBigO_input :
    (fun n : ℕ => ((DFTModelInitialPreparation.budget n+
      DFTModelCacheAllAxisForests.workBudget n+calendarBudget n : ℕ) : ℝ))
      =O[atTop] (fun n : ℕ => (n : ℝ)) := by
  simpa only [Nat.cast_add] using
    (DFTModelInitialPreparation.budget_isBigO_input.add all_axis_budget_isBigO_input).add
      calendar_budget_isBigO_input

end
end ExactFourierCircuits.DFTModelCacheAsymptotics

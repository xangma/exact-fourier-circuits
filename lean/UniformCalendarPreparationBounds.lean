import UniformCalendarClockBounds
import UniformJointCacheTime

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarPreparationBounds
open UniformBalancedToeplitz UniformJointCacheExtent UniformJointCacheTime
open UniformCalendarClockBounds
open scoped BigOperators
noncomputable section

/-- Both genuine direct orientations and every actual rectangle cache slot. -/
def calendarEntries {r:ℕ}(P:Plan r):ℕ:=
 ((UniformLocalPreparationDAG.requests P (le_refl r)).map (fun q=>slotCount q.k)).sum+2*leafOperations P
lemma entries_bound {r:ℕ}(P:Plan r):calendarEntries P ≤ capacity r:=full_slots_bound r P

/-- Static costs of the literal15 factor merger and literal23 row printer,
including the dispatcher's reader, headers and loop edges. These arithmetic
bounds do not claim that the dispatcher has executed. -/
def factorTicks(r kind:ℕ):ℕ:=9*r+if kind=0 then 46 else 37
def matchingTicks(pairs kind:ℕ):ℕ:=16*pairs+if kind=2 then 37 else 48
lemma factor_bound(r kind:ℕ):factorTicks r kind ≤ 9*r+48:=by
 unfold factorTicks;split_ifs <;>omega
lemma matching_bound(r pairs kind:ℕ)(geometry:2*pairs ≤ r):
 matchingTicks pairs kind ≤ 9*r+48:=by
 unfold matchingTicks;split_ifs <;>omega

/-- Includes the entire selector scan, phase-bank printer, pool initialization,
all selected-entry dispatches and final negative branches. -/
def preparationBudget(r N:ℕ):ℕ:=45*r+199+N*(9*r+69)
lemma selection_sum {α:Type}(L:List α)(cost:α → ℕ)(r:ℕ)
 (each:∀e∈L,cost e ≤ 9*r+48):
 (L.map cost).sum ≤ L.length*(9*r+48):=by
 exact (UniformJointCacheExtent.sum_bound _ _ (by
  intro v hv
  obtain ⟨e,he,rfl⟩:=List.mem_map.mp hv
  exact each e he)).trans_eq (by rw [List.length_map])
lemma selector_dispatch(r N selected entryWork:ℕ)(count:selected ≤ N)
 (entries:entryWork ≤ selected*(9*r+48)):
 (21*N+8)+(45*r+191+entryWork) ≤ preparationBudget r N:=by
 have demand:=Nat.mul_le_mul_right (9*r+48) count
 unfold preparationBudget
 nlinarith only[entries,demand]
lemma capacity_mono {r R:ℕ}(h:r ≤ R):capacity r ≤ capacity R:=by
 have log:=Nat.clog_mono_right 2 (Nat.mul_le_mul_left 4 h)
 have slots:=slotCount_mono log
 exact Nat.mul_le_mul (Nat.pow_le_pow_left h 2) (by omega)
lemma preparation_mono {r R N M:ℕ}(radix:r ≤ R)(count:N ≤ M):
 preparationBudget r N ≤ preparationBudget R M:=by
 have product:=Nat.mul_le_mul count (show 9*r+69 ≤ 9*R+69 by omega)
 unfold preparationBudget
 omega
lemma actual_plan_budget {r:ℕ}(P:Plan r):
 preparationBudget r (calendarEntries P) ≤ preparationBudget r (capacity r):=
 preparation_mono (le_refl r) (entries_bound P)

def allAxesBudget(n:ℕ):ℕ:=∑j,preparationBudget
 (UniformSelectedCRT.radices n j) (capacity (UniformSelectedCRT.radices n j))
lemma selected_axis_budget {n:ℕ}(hn:0<n)(j:Fin (UniformWorkingLength.axisCount n+1)):
 preparationBudget (UniformSelectedCRT.radices n j) (capacity (UniformSelectedCRT.radices n j)) ≤ 
 preparationBudget (radixCap n) (capacity (radixCap n)):=by
 exact preparation_mono (selected_radix hn j) (capacity_mono (selected_radix hn j))
lemma all_axes_bound {n:ℕ}(hn:0<n):
 allAxesBudget n ≤ (UniformWorkingLength.axisCount n+1)*preparationBudget (radixCap n) (capacity (radixCap n)):=by
 unfold allAxesBudget
 have h:=Finset.sum_le_sum (fun j (_:j∈Finset.univ)=>selected_axis_budget hn j)
 simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using h
lemma all_clocks_preparation {n:ℕ}(hn:0<n):
 synchronizedDepth n*allAxesBudget n ≤ clockCap n*((UniformWorkingLength.axisCount n+1)*
 preparationBudget (radixCap n) (capacity (radixCap n))):=
 Nat.mul_le_mul (synchronized_bound hn) (all_axes_bound hn)
end
end ExactFourierCircuits.UniformCalendarPreparationBounds

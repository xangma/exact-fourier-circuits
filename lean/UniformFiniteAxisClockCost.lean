import UniformCanonicalClockStepCost
import UniformFinalFiniteAxisAdvance

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFiniteAxisClockCost
noncomputable section
open UniformMachine UniformAllAxisSeedPreparation UniformSynchronizedLayers
open UniformActualGlobalConstants (constants)
attribute [local irreducible] Nat.add Nat.mul UniformRecursiveSavingProgram.program

variable {n:ℕ}(hn:0<n){s:State}
 (cache:∀j:Fin (axisCount n),UniformAxisCacheContents.Contents constants n hn j s)

lemma axis_eq (g:ℕ)(j:Fin (axisCount n)):
 UniformFinalFiniteAxisAdvance.axisCost hn cache g j.val=
 UniformCanonicalAxisCost.axisCost hn cache g j:=by
 unfold UniformFinalFiniteAxisAdvance.axisCost
 rw[dite_eq_left j.isLt]
 dsimp only
 rw[UniformFourierAxisCommonInputs.records_count]
 rfl

lemma sum_eq (g:ℕ):
 (∑k∈Finset.range (axisCount n),UniformFinalFiniteAxisAdvance.axisCost hn cache g k)=
 ∑j:Fin (axisCount n),UniformCanonicalAxisCost.axisCost hn cache g j:=by
 calc
  _=(∑j:Fin (axisCount n),UniformFinalFiniteAxisAdvance.axisCost hn cache g j.val):=
   (Fin.sum_univ_eq_sum_range (UniformFinalFiniteAxisAdvance.axisCost hn cache g) (axisCount n)).symm
  _= _:=Finset.sum_congr rfl (fun j _=>axis_eq hn cache g j)

lemma axes_bound (g:ℕ):
 (∑k∈Finset.range (axisCount n),UniformFinalFiniteAxisAdvance.axisCost hn cache g k)≤
 UniformFinalClockOverhead.axesScanBudget n:=by
 rw[sum_eq]
 exact Finset.sum_le_sum (fun j _=>UniformCanonicalAxisCost.bound hn cache g j)

/-- This is the exact Nat allowance returned by actual finiteaxes.execution,
followed by the actual prepared kernel/diagonal tick. -/
theorem prepared_step_bound {H:ℕ}
 (length:∀j,(localSchedules n j).length≤H)(t:Fin H)
 (actual:∀j,UniformCalendarAxisAction.Action (UniformAllAxisSeedPreparation.radix n j)
  (UniformFinalAxisPrinted.events hn cache t.val j)
  (UniformSynchronizedLayers.slot (localSchedules n j) (length j) t).matrix):
 ((∑k∈Finset.range (axisCount n),UniformFinalFiniteAxisAdvance.axisCost hn cache t.val k)+6+
  UniformProducedClockTickPrepared.budget hn (UniformFinalAxisPrinted.events hn cache t.val) length t actual:ℝ)≤
 UniformCanonicalClockStepCost.stepEnvelope constants.roles n:=by
 have bound:=UniformCanonicalClockStepCost.prepared_step_bound hn cache length t actual
 rw[sum_eq]
 linarith only[bound]

end
end ExactFourierCircuits.UniformFiniteAxisClockCost

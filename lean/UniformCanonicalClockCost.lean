import UniformCanonicalAxisCost
import UniformActualProducedTickCost
import UniformProducedClockTick

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCanonicalClockCost
noncomputable section
open UniformMachine UniformAllAxisSeedPreparation UniformSynchronizedLayers
open UniformActualGlobalConstants (constants roles_positive)
open UniformCanonicalAxisCost
attribute [local irreducible] Nat.add Nat.mul UniformRecursiveSavingProgram.program

lemma specified_length (r:ℕ)(positive:0<r):
 (UniformLocalFourierLayers.specifiedSchedule r).length=
  2*UniformLocalCacheTiming.planDuration (UniformBalancedToeplitz.plan r)+5:=by
 rw[UniformLocalFourierLayers.specifiedSchedule,dite_eq_left positive,
  UniformLocalFourierLayers.schedule,UniformLocalFourierLayers.symmetric_length]
 unfold UniformLocalFourierLayers.Nschedule UniformLocalFourierLayers.sandwich UniformLocalFourierLayers.toeplitz
 simp only[List.length_append,List.length_singleton,UniformLocalCacheTiming.render_duration]
 omega

lemma length {n:ℕ}(hn:0<n)(j:Fin (axisCount n)):
 (localSchedules n j).length≤UniformFourierClockBounds.horizon n:=by
 have two:=UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn j
 rw[localSchedules,specified_length (UniformSelectedCRT.radices n j) (by omega)]
 exact UniformFourierClockBounds.selected_le n j

variable {n:ℕ}(hn:0<n){s:State}
 (cache:∀j:Fin (axisCount n),UniformAxisCacheContents.Contents constants n hn j s)

def action (t:Fin (UniformFourierClockBounds.horizon n))(j:Fin (axisCount n)):
 UniformCalendarAxisAction.Action (UniformAllAxisSeedPreparation.radix n j)
  (UniformFinalAxisPrinted.events hn cache t.val j)
  (UniformSynchronizedLayers.slot (localSchedules n j) (length hn j) t).matrix:=by
 apply UniformCalendarAxisAction.congr (UniformFinalAxisPrinted.action hn cache t.val j)
 exact (UniformReflectedFourierCalendar.specified_matrix (UniformAllAxisSeedPreparation.radix n j) t.val).trans
  (UniformAllAxisCalendarTensor.slot_tick (localSchedules n j) (length hn j) t).symm

def geometry (t:Fin (UniformFourierClockBounds.horizon n)):
 UniformActualGlobalTickContext.Geometry n:=
 UniformProducedAllAxisGeometry.geometry
  (UniformProducedClockTick.family hn (UniformFinalAxisPrinted.events hn cache t.val)
   (length hn) t (action hn cache t))

def retainedBudget (t:Fin (UniformFourierClockBounds.horizon n)):ℕ:=
 UniformGlobalKernelDiagonalRetention.budget
  (UniformActualGlobalTickContext.kernel hn (geometry hn cache t))
  (UniformActualGlobalTickContext.diagonal hn (geometry hn cache t))
  UniformRecursiveChildInduction.cost

def loopBudget:ℕ:=UniformFinalClockCost.loopBudget n
 (fun _ j=>prep n j) (fun t j=>selected hn cache t.val j) (retainedBudget hn cache)

/-- All geometry, links, radix bounds, scan bounds and selected-event counts
are derived from the actual canonical cache/action family. -/
theorem bound:(loopBudget hn cache:ℝ)≤UniformFinalClockCost.clockEnvelope constants.roles n:=by
 apply UniformFinalClockCost.actual_loop_bound constants hn roles_positive
  (fun t=>(geometry hn cache t).physical)
  (fun t=>(geometry hn cache t).placement.shape)
  (fun _ j=>prep n j) (fun t j=>selected hn cache t.val j) (retainedBudget hn cache)
 · intro t j
   exact UniformCanonicalAxisCost.bound hn cache t.val j
 · intro t
   exact UniformActualProducedTickCost.retention_bound hn (geometry hn cache t)

/-- Exact budget shape returned by the concrete finite-axis loop and the
actual produced kernel/diagonal clock consumer, including their6+2 controls. -/
def actualBudget:ℕ:=7+Finset.univ.sum (fun t:Fin (UniformFourierClockBounds.horizon n)=>
 6+(∑j:Fin (axisCount n),UniformCanonicalAxisCost.axisCost hn cache t.val j)+
 UniformProducedClockTick.budget hn (UniformFinalAxisPrinted.events hn cache t.val)
  (length hn) t (action hn cache t))

lemma actual_eq:actualBudget hn cache=loopBudget hn cache:=by
 have tick(t:Fin (UniformFourierClockBounds.horizon n)):
  UniformProducedClockTick.budget hn (UniformFinalAxisPrinted.events hn cache t.val)
   (length hn) t (action hn cache t)=retainedBudget hn cache t+2:=rfl
 unfold actualBudget loopBudget UniformFinalClockCost.loopBudget
 simp only[tick,UniformCanonicalAxisCost.axisCost]
 congr 1
 apply Finset.sum_congr rfl
 intro t _
 omega

theorem actual_bound:(actualBudget hn cache:ℝ)≤UniformFinalClockCost.clockEnvelope constants.roles n:=by
 rw[actual_eq]
 exact bound hn cache

lemma prepared_budget (t:Fin (UniformFourierClockBounds.horizon n)):
 UniformProducedClockTickPrepared.budget hn (UniformFinalAxisPrinted.events hn cache t.val)
  (length hn) t (action hn cache t)=
 UniformProducedClockTick.budget hn (UniformFinalAxisPrinted.events hn cache t.val)
  (length hn) t (action hn cache t):=rfl

end
end ExactFourierCircuits.UniformCanonicalClockCost

import UniformCanonicalClockCost

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCanonicalClockStepCost
noncomputable section
open UniformMachine UniformAllAxisSeedPreparation UniformSynchronizedLayers
open UniformActualGlobalConstants (constants roles_positive)
open UniformFinalClockOverhead
attribute [local irreducible] Nat.add Nat.mul UniformRecursiveSavingProgram.program

/-- A single real allowance is independent of the current heap and of every
chosen call enumeration in the actual prepared family. -/
def stepEnvelope (W n:ℕ):ℝ:=(8+axesScanBudget n:ℕ)+
 UniformActualKernelCost.clockConstant W*((UniformWorkingLength.axisCount n+2:ℕ):ℝ)^UniformExponent.theta*
 UniformWorkingLength.workingLength n+((130*W+100)*UniformInitialPreparation.len n:ℕ)

lemma retention_real {n:ℕ}(hn:0<n)(a:UniformActualGlobalTickContext.Geometry n):
 (UniformGlobalKernelDiagonalRetention.budget
  (UniformActualGlobalTickContext.kernel hn a) (UniformActualGlobalTickContext.diagonal hn a)
  UniformRecursiveChildInduction.cost:ℝ)≤
 UniformActualKernelCost.clockConstant constants.roles*((UniformWorkingLength.axisCount n+2:ℕ):ℝ)^UniformExponent.theta*
 UniformWorkingLength.workingLength n+((130*constants.roles+100)*UniformInitialPreparation.len n:ℕ):=by
 have numeric:=UniformActualProducedTickCost.retention_bound hn a
 have casted:(UniformGlobalKernelDiagonalRetention.budget
  (UniformActualGlobalTickContext.kernel hn a) (UniformActualGlobalTickContext.diagonal hn a)
  UniformRecursiveChildInduction.cost:ℝ)≤
 (UniformActualKernelCost.kernelTicks (UniformJointConditionalKernelContext.actualReserveContext
  constants n hn roles_positive a.physical a.placement.shape):ℝ)+
 ((130*constants.roles+100)*UniformInitialPreparation.len n:ℕ):=by exact_mod_cast numeric
 have kernel:=UniformActualSelectedKernelCost.selected_kernel constants hn roles_positive a.physical a.placement.shape
 linarith only[casted,kernel]

/-- Actual finiteaxes6 plus the actual retained kernel/diagonal2. The initial
cache factory derives counts; any genuine Action enumeration has the same
uniform geometry bound. No selected-count or desired-cost premise is supplied. -/
theorem actual_step_bound {n H:ℕ}(hn:0<n){s:State}
 (cache:∀j:Fin (axisCount n),UniformAxisCacheContents.Contents constants n hn j s)
 (length:∀j,(localSchedules n j).length≤H)(t:Fin H)
 (actual:∀j,UniformCalendarAxisAction.Action (UniformAllAxisSeedPreparation.radix n j)
  (UniformFinalAxisPrinted.events hn cache t.val j)
  (UniformSynchronizedLayers.slot (localSchedules n j) (length j) t).matrix):
 (6+(∑j:Fin (axisCount n),UniformCanonicalAxisCost.axisCost hn cache t.val j)+
  UniformProducedClockTick.budget hn (UniformFinalAxisPrinted.events hn cache t.val) length t actual:ℝ)≤
 stepEnvelope constants.roles n:=by
 let a:=UniformProducedAllAxisGeometry.geometry
  (UniformProducedClockTick.family hn (UniformFinalAxisPrinted.events hn cache t.val) length t actual)
 let K:=UniformGlobalKernelDiagonalRetention.budget
  (UniformActualGlobalTickContext.kernel hn a) (UniformActualGlobalTickContext.diagonal hn a)
  UniformRecursiveChildInduction.cost
 have tick:UniformProducedClockTick.budget hn (UniformFinalAxisPrinted.events hn cache t.val) length t actual=K+2:=rfl
 have axes:(∑j:Fin (axisCount n),UniformCanonicalAxisCost.axisCost hn cache t.val j)≤axesScanBudget n:=
  Finset.sum_le_sum (fun j _=>UniformCanonicalAxisCost.bound hn cache t.val j)
 have small:6+(∑j:Fin (axisCount n),UniformCanonicalAxisCost.axisCost hn cache t.val j)+
  UniformProducedClockTick.budget hn (UniformFinalAxisPrinted.events hn cache t.val) length t actual≤8+axesScanBudget n+K:=by
  rw[tick];omega
 have casted:(6+(∑j:Fin (axisCount n),UniformCanonicalAxisCost.axisCost hn cache t.val j)+
  UniformProducedClockTick.budget hn (UniformFinalAxisPrinted.events hn cache t.val) length t actual:ℝ)≤
  (8+axesScanBudget n:ℕ)+(K:ℝ):=by exact_mod_cast small
 have cost:=retention_real hn a
 dsimp only[K] at casted
 unfold stepEnvelope
 linarith only[casted,cost]

theorem prepared_step_bound {n H:ℕ}(hn:0<n){s:State}
 (cache:∀j:Fin (axisCount n),UniformAxisCacheContents.Contents constants n hn j s)
 (length:∀j,(localSchedules n j).length≤H)(t:Fin H)
 (actual:∀j,UniformCalendarAxisAction.Action (UniformAllAxisSeedPreparation.radix n j)
  (UniformFinalAxisPrinted.events hn cache t.val j)
  (UniformSynchronizedLayers.slot (localSchedules n j) (length j) t).matrix):
 (6+(∑j:Fin (axisCount n),UniformCanonicalAxisCost.axisCost hn cache t.val j)+
  UniformProducedClockTickPrepared.budget hn (UniformFinalAxisPrinted.events hn cache t.val) length t actual:ℝ)≤
 stepEnvelope constants.roles n:=by
 change (6+(∑j:Fin (axisCount n),UniformCanonicalAxisCost.axisCost hn cache t.val j)+
  UniformProducedClockTick.budget hn (UniformFinalAxisPrinted.events hn cache t.val) length t actual:ℝ)≤_
 exact actual_step_bound hn cache length t actual

lemma nonneg (W n:ℕ):0 ≤ stepEnvelope W n:=by
 unfold stepEnvelope
 have positive:=UniformActualKernelCost.clockConstant_nonneg W
 positivity

/-- The actual full horizon folds the pointwise allowance to precisely the
already certified clock envelope. -/
lemma envelope_eq (W n:ℕ):
 7+(UniformFourierClockBounds.horizon n:ℝ)*stepEnvelope W n=UniformFinalClockCost.clockEnvelope W n:=by
 unfold stepEnvelope UniformFinalClockCost.clockEnvelope clockScanBudget
  UniformActualCalendarAsymptotics.kernelEnvelope UniformFinalClockCost.diagonalBudget
 push_cast
 ring

/-- Fully canonical specialization: only genuine retained cache Contents are
inputs; geometry, ordered action, horizon and all count/cost bounds are built. -/
theorem canonical_bound {n:ℕ}(hn:0<n){s:State}
 (cache:∀j:Fin (axisCount n),UniformAxisCacheContents.Contents constants n hn j s)
 (t:Fin (UniformFourierClockBounds.horizon n)):
 (6+(∑j:Fin (axisCount n),UniformCanonicalAxisCost.axisCost hn cache t.val j)+
  UniformProducedClockTick.budget hn (UniformFinalAxisPrinted.events hn cache t.val)
   (UniformCanonicalClockCost.length hn) t (UniformCanonicalClockCost.action hn cache t):ℝ)≤
 stepEnvelope constants.roles n:=
 actual_step_bound hn cache (UniformCanonicalClockCost.length hn) t (UniformCanonicalClockCost.action hn cache t)

end
end ExactFourierCircuits.UniformCanonicalClockStepCost

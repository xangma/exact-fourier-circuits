import UniformFinalFiniteAxes
import UniformCanonicalClockStepCost
import UniformProducedClockTickTracked
import UniformActualClockReadyAfterKernel
import UniformActualClockNumericInvariant
import UniformActualClockOuterFrameConstruction
/-!
Paper correspondence (audit): *An explicit power saving for the exact discrete Fourier transform*,
OpenAI math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
§4.3, Proposition 4.2 proof, PDF p. 20 (`prop:tensor-fourier`), and §2.6, Theorem 2.6, pp. 11–12 (`net:tensor-bound`).

This closes local Action and printed-bank inputs with actual finite-axis preparation, then joins the actual recursive kernel/diagonal execution through the same intermediate state. Integral instruction counts are compared to a uniform real theta allowance.
-/

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCompleteClockTick
open UniformMachine UniformAllAxisSeedPreparation UniformSynchronizedLayers
open UniformActualGlobalConstants (constants)
open UniformActualClockReady UniformActualClockNumericInvariant UniformFinalClockOuterRetention
open UniformTensorMonomialMachine (setPC)
open scoped BigOperators
noncomputable section
attribute [local irreducible] Nat.add UniformRecursiveSavingProgram.program

lemma axis_cost {n:ℕ}(hn:0<n){s:State}
 (cache:∀i:Fin (axisCount n),UniformAxisCacheContents.Contents constants n hn i s)(g:ℕ):
 (∑k∈Finset.range (axisCount n),UniformFinalFiniteAxisAdvance.axisCost hn cache g k)=
 ∑j:Fin (axisCount n),UniformCanonicalAxisCost.axisCost hn cache g j:=by
 rw[←Fin.sum_univ_eq_sum_range]
 apply Finset.sum_congr rfl
 intro j _
 unfold UniformFinalFiniteAxisAdvance.axisCost
 rw[dite_eq_left j.isLt]
 dsimp only
 unfold UniformCanonicalAxisCost.axisCost UniformCanonicalAxisCost.prep UniformCanonicalAxisCost.selected
 rw[UniformFourierAxisCommonInputs.records_count]

/-- One fully instantiated clock iteration: actual finite axes, actual same
recursive kernel and actual147 diagonal. No action or advance premise remains. -/
theorem execution {n t:ℕ}(hn:0<n)(x:Fin n→ℂ)
 (initial v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar)(s:State)
 (ready:Ready hn (UniformFourierClockBounds.horizon n) (directoryBase n) x t v s)
 (unfinished:t<UniformFourierClockBounds.horizon n)
 (history:Prefix n (UniformFourierClockBounds.horizon n) ready.length initial t s)
 (prepared:UniformActualClockEntry.Prepared initial→UniformActualClockEntry.Prepared v):
 ∃u ticks w,BoundedRuns UniformActualGlobalClockProgram.program n x (UniformJointAllocation.envelope constants n) s ticks u∧
 (ticks:ℝ)≤UniformCanonicalClockStepCost.stepEnvelope constants.roles n∧
 Ready hn (UniformFourierClockBounds.horizon n) (directoryBase n) x (t+1) w u∧
 Prefix n (UniformFourierClockBounds.horizon n) ready.length initial (t+1) u∧
 (UniformActualClockEntry.Prepared initial→UniformActualClockEntry.Prepared w)∧
 Frame n s u∧Spectrum n s u∧
 u.natReg 6819=UniformGlobalCalendarArena.natBase constants n∧
 u.natReg 6821=UniformGlobalCalendarArena.scalarBase constants n:=by
 /- Proposition 4.2 proof, p. 20: retained cache contents determine each local compiled action; finite-axis execution physically prints those exact actions at this clock. -/
 let cache:=UniformFinalFiniteAxes.cache ready
 let time:Fin (UniformFourierClockBounds.horizon n):=⟨t,unfinished⟩
 let actual:=UniformCanonicalClockCost.action hn cache time
 obtain ⟨a,axisTicks,axes,axesCheap,apc,printed,atReady,retained,seed,natEnd,scalarEnd⟩:=
  UniformFinalFiniteAxes.execution hn x v s ready unfinished
 have printed':UniformCalendarPrintedPrefix.Printed hn
  (UniformFinalAxisPrinted.events hn cache t) (fun i=>(actual i).position) (axisCount n) a:=printed
 /- Proposition 4.2 proof, p. 20: the real intermediate state `a` from axis printing is the kernel’s entry. `axes.trans kernel` joins these actual executions and charges both. -/
 obtain ⟨u,kt,kernel,kernelCheap,pc,clock,source,numeric,tags,nat,scalar,outputs,roots,clockFrame,high,startup⟩:=
  UniformProducedClockTickTracked.execution hn (UniformFinalAxisPrinted.events hn cache t)
   (UniformCanonicalClockCost.length hn) time actual v x a printed' atReady.source
   (UniformActualClockEntry.Prepared initial) prepared atReady.volume atReady.axisCount atReady.allocator
   atReady.constants apc axes.final_bound atReady.one atReady.clock atReady.horizon
 have next:=UniformActualClockReadyAfterKernel.restore hn x v (UniformProducedClockTick.stored n u) a u
  atReady pc kernel.final_bound clock source nat scalar outputs roots clockFrame high startup
 have before:Prefix n (UniformFourierClockBounds.horizon n) ready.length initial t a:=
  UniformActualClockNumericInvariant.transport ready.length initial s a history
   (fun r hr j=>retained.scalarHigh _ (by unfold UniformActualClockEntry.sourceBase UniformKernelSpectrumStorage.base;omega))
 have advanced:=UniformActualClockNumericInvariant.step ready.length initial v
  (UniformProducedClockTick.stored n u) time a u before atReady.source source numeric
 have axesFrame:=UniformActualClockOuterFrameConstruction.axis axes retained
 have kernelFrame:=UniformActualClockOuterFrameConstruction.low_two hn kernel nat scalar outputs roots
 /- Equation (4.4), pp. 19–20: sector widths and pair counts discharge the kernel theta bound; concrete per-axis preparation and control ticks are added before comparing to the uniform real allowance. -/
 have cost:=UniformCanonicalClockStepCost.actual_step_bound hn cache (UniformCanonicalClockCost.length hn) time actual
 have axisEq:=axis_cost hn cache t
 have wholeCheap:axisTicks+kt≤6+(∑j:Fin (axisCount n),UniformCanonicalAxisCost.axisCost hn cache t j)+
  UniformProducedClockTick.budget hn (UniformFinalAxisPrinted.events hn cache t) (UniformCanonicalClockCost.length hn) time actual:=by
  rw[axisEq] at axesCheap
  omega
 refine ⟨u,axisTicks+kt,UniformProducedClockTick.stored n u,axes.trans kernel,?_,next,advanced,tags,
  axesFrame.1.trans kernelFrame.1,UniformActualClockOuterFrameConstruction.Spectrum.trans axesFrame.2 kernelFrame.2,?_,?_⟩
 · have casted:((axisTicks+kt:ℕ):ℝ)≤((6+(∑j:Fin (axisCount n),UniformCanonicalAxisCost.axisCost hn cache t j)+
    UniformProducedClockTick.budget hn (UniformFinalAxisPrinted.events hn cache t) (UniformCanonicalClockCost.length hn) time actual:ℕ):ℝ):=by exact_mod_cast wholeCheap
   push_cast at casted cost
   simpa only[Nat.cast_add] using casted.trans cost
 · exact (high 6819 (by omega)).trans natEnd
 · exact (high 6821 (by omega)).trans scalarEnd
end
end ExactFourierCircuits.UniformActualCompleteClockTick

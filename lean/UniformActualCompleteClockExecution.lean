import UniformActualCompleteClockResult
import UniformActualCompleteClockTick
import UniformActualClockRealInduction
set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCompleteClockExecution
open UniformMachine UniformAllAxisSeedPreparation
open UniformActualGlobalConstants (constants)
open UniformActualClockReady UniformActualClockNumericInvariant UniformFinalClockOuterRetention
open UniformTensorMonomialMachine (setPC applyBlock)
noncomputable section
attribute [local irreducible] Nat.add UniformRecursiveSavingProgram.program UniformActualGlobalClockProgram.program

/-- The complete literal Fourier clock: charged boot, every actual axis and
clock iteration, then the charged terminal branch and halt. Numerical values
and collective prepared tags are established by the same physical execution. -/
theorem execution {n:ℕ}(hn:0<n)(x:Fin n→ℂ)
 (v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar)(s:State)
 (entry:UniformActualClockEntry.Input n (UniformFourierClockBounds.horizon n) (directoryBase n) v s)
 (inputs:UniformAxisCacheInputs.Inputs n x s)
 (cache:UniformAxisCacheLoopState.All constants n hn (axisCount n) s):
 ∃u ticks,BoundedExecution UniformActualGlobalClockProgram.program n x (UniformJointAllocation.envelope constants n) s ticks u∧
 (ticks:ℝ)≤UniformFinalClockCost.clockEnvelope constants.roles n∧Output hn x v s u:=by
 let H:=UniformFourierClockBounds.horizon n
 let allowance:=UniformCanonicalClockStepCost.stepEnvelope constants.roles n
 let I(k:ℕ)(a:State):Prop:=∃w,
  Ready hn H (directoryBase n) x k w a∧
  Prefix n H entry.length v k a∧
  (UniformActualClockEntry.Prepared v→UniformActualClockEntry.Prepared w)∧
  Frame n s a∧Spectrum n s a∧
  a.natReg 6819=UniformGlobalCalendarArena.natBase constants n∧
  a.natReg 6821=UniformGlobalCalendarArena.scalarBase constants n
 obtain ⟨boot,ready⟩:=UniformActualClockReady.boot_execution hn x v s entry inputs cache
 let start:=applyBlock UniformGlobalClockConductor.boot s
 have bootFrame:=UniformActualClockOuterFrameConstruction.low_two hn boot
  (fun _ _=>rfl) (fun _ _=>rfl) rfl rfl
 have initial:I 0 start:=by
  refine ⟨v,ready,?_,fun h=>h,bootFrame.1,bootFrame.2,?_,?_⟩
  · exact UniformActualClockNumericInvariant.initial entry.length v start ready.source
  · exact entry.natFrontier
  · exact entry.scalarFrontier
 obtain ⟨a,ticks,run,cheap,done⟩:=UniformActualClockRealInduction.clocks x I allowance start initial boot.final_bound entry.code
  (fun k a h=>by obtain ⟨w,ready,_⟩:=h;exact ⟨ready.pc,ready.clock,ready.horizon⟩)
  (fun k hk a h bound=>by
   obtain ⟨w,ready,history,tags,frame,spectrum,natEnd,scalarEnd⟩:=h
   obtain ⟨u,t,w',next,nextCheap,nextReady,nextPrefix,nextTags,nextFrame,nextSpectrum,nextNat,nextScalar⟩:=
    UniformActualCompleteClockTick.execution hn x v w a ready hk history tags
   exact ⟨u,t,next,nextCheap,w',nextReady,nextPrefix,nextTags,frame.trans nextFrame,
    UniformActualClockOuterFrameConstruction.Spectrum.trans spectrum nextSpectrum,nextNat,nextScalar⟩)
 obtain ⟨w,finished,history,tags,frame,spectrum,natEnd,scalarEnd⟩:=done
 let terminal:=setPC a (UniformGlobalClockConductor.finalPC UniformFourierAxisPrepareMachine.program
  UniformRecursiveSavingProgram.program UniformRecursiveSelfCallMachine.W)
 have numeric:UniformActualClockEntry.Numeric n v terminal:=
  UniformActualClockNumericInvariant.final entry.length v a history
 have prepared:UniformActualClockEntry.Prepared v→UniformActualClockEntry.PreparedOutput n terminal:=by
  intro h
  exact UniformActualClockNumericInvariant.prepared w a finished.source (tags h)
 have runtime:UniformFinalClockRuntime.Runtime n terminal:=
  ⟨finished.allocator,finished.horizon,natEnd,scalarEnd,finished.seed,finished.initialNat,finished.initialScalar⟩
 refine ⟨terminal,5+ticks,boot.executes run,?_,numeric,prepared,frame.withPC _,spectrum,runtime⟩
 have equality:=UniformCanonicalClockStepCost.envelope_eq constants.roles n
 push_cast
 change (ticks:ℝ)≤(H:ℝ)*allowance+2 at cheap
 change 7+(H:ℝ)*allowance=_ at equality
 linarith only[cheap,equality]
end
end ExactFourierCircuits.UniformActualCompleteClockExecution

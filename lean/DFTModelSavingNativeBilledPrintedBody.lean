import DFTModelSavingNativeBilledWholeSchedule
import DFTModelSavingNativePrintedBody
import DFTModelSavingCostBilledLarge
import DFTModelSavingBinaryCost
import DFTModelSavingNativeNode
import DFTModelSavingNativeTerminal
import UniformRecursivePrintedBody

set_option autoImplicit false

/-! Paper E, revision adc7f1241b42e322a6451854ab7e4b4c146bf78a,
§2.4, Proposition 2.4, p.10; §2.6, Theorem 2.6, pp.11–12.
The actual printed fixed network, padding and spectator suffix form one
continuous source execution and one typed paired computation. -/
namespace ExactFourierCircuits.DFTModelSavingNativeBilledPrintedBody
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine
open UniformNativeScheduleSemantics UniformRecursiveTypedBody
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursiveResidualEdge (Parent)
open DFTModelClockControl DFTModelAdmissibilityControl
open DFTModelRecursiveScalarSource (paired)
namespace P
export UniformRecursiveSavingProgram (program address seedLength unitLength unitRecord)
end P
noncomputable section
attribute [local irreducible] P.program DFTModelSavingBinarySuffix.program
  DFTModelSavingProgram.large DFTModelSavingRecords.stream DFTModelCacheRecords.seed

/-- Finish the same billed prefix with the actual terminal suffix. The
comparison includes the caller's positive source prefix and all source ticks. -/
theorem finish (n B T U A F H q rest stack depth stackTop reserve K prefixTicks : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (h : Handler ChildPort)
    (s s0 : State) (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (t t0 : State) (first : ℕ) (g g0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (body : DFTModelSavingNativeWholeSchedule.Result n B T U A F H q rest stack depth stackTop
      cost x Complex.I h s s0 t t0 first f f0 g g0)
    (stream : ((DFTModelSavingRecords.stream W).run h
      (rest,((run DFTModelCacheRecords.seed q).val,((q*m+rest,Complex.I),paired f f0)))).work≤K*first+12)
    (geometry : Geometry B A F q rest stack depth stackTop reserve)
    (metadata : s.natHeap (F-1)=some (T+P.seedLength))
    (cap : DFTModelSavingCost.nativeWorkFactor≤K) (positive : 1≤prefixTicks) :
    ∃u u0 final final0,
      DFTModelSavingNativePrintedBody.Result n B T U A F H q rest stack depth stackTop cost x h
        s s0 u u0 (first+(4*(q*m)+W*UniformBinarySpectatorCMachine.arrayCost (q*m+rest) (q*m)+20))
        f f0 final final0 ∧
      (Code.run DFTModelSavingProgram.large h ((q*m+rest,Complex.I),paired f f0)).work+27≤
        K*(prefixTicks+(first+(4*(q*m)+W*UniformBinarySpectatorCMachine.arrayCost (q*m+rest) (q*m)+20))) := by
  obtain ⟨u,u0,final,final0,result⟩:=DFTModelSavingNativePrintedBody.finish
    n B T U A F H q rest stack depth stackTop reserve cost x h s s0 f f0 t t0 first g g0 body geometry metadata
  refine ⟨u,u0,final,final0,result,?_⟩
  obtain ⟨qr,rr⟩:=DFTModelSavingNativeNode.quotient_remainder q rest geometry.remainder
  have mp : 0 < m :=by norm_num [m,ExplicitSeedBudget.m]
  have qm:0<q*m:=Nat.mul_pos (by have p:=geometry.positive;omega) mp
  have kp:0<q*m+rest:=by omega
  have len:(paired f f0).len=UniformBatching.width*2^(q*m+rest):=rfl
  have even:2*((paired f f0).len/2)=(paired f f0).len:=
    DFTModelSavingBinary.volume_even W (q*m+rest) kp
  have width : W=UniformBatching.width := rfl
  have comparison:=DFTModelSavingCost.large_native_billed_work h (q*m+rest) K prefixTicks first
    Complex.I (paired f f0) even len
      (by simpa only [qr,rr,width] using stream)
      (DFTModelSavingCost.factor_preparation.trans cap)
      (DFTModelSavingCost.factor_suffix.trans cap) positive
  simpa only [qr,width,Nat.add_assoc] using comparison

/-- The actual source schedule and terminal suffix provide one measured work
comparison for the compiled large branch. Smaller paired source calls are the
only internal induction premise. -/
theorem execution (n B T U A F H q rest stack depth stackTop reserve K prefixTicks : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (h : Handler ChildPort)
    (s s0 : State) (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (childIH : DFTModelSavingResidualNativeGroup.BilledPairSmallerBodies
      (q*m+rest) n B reserve stack stackTop K K cost x Complex.I h)
    (cap : DFTModelSavingCost.nativeWorkFactor≤K) (positive : 1≤prefixTicks)
    (geometry : Geometry B A F q rest stack depth stackTop reserve)
    (same : StateMatch s s0) (pc : s.pc=P.address .loop)
    (parent : Parent (q*m+rest) q A F T rest stack depth s)
    (metadata : s.natHeap (F-1)=some (T+P.seedLength))
    (printed : PrintedRecords T (scheduleRecords q) s)
    (data : Present A W (2^(q*m+rest)) f s) (data0 : Present A W (2^(q*m+rest)) f0 s0)
    (unitPointer : s.natHeap (F-2)=some U)
    (unitPrinted : Printed U (P.unitRecord.withColumns q).data s)
    (mainEnd : T+P.seedLength≤F-6) (unitEnd : U+P.unitLength≤F-6)
    (stackEnd : stackTop≤T) (unitAbove : stackTop≤U)
    (floorUnit : H≤U) (floorWork : H≤F-6)
    (constants : UniformBinaryCStageMachine.Constants s) (bound : WordBound B s) :
    ∃u u0 time g g0,DFTModelSavingNativePrintedBody.Result n B T U A F H q rest stack depth stackTop cost x h
      s s0 u u0 time f f0 g g0 ∧
      (Code.run DFTModelSavingProgram.large h ((q*m+rest,Complex.I),paired f f0)).work+27≤
        K*(prefixTicks+time) := by
  obtain ⟨t,t0,first,g,g0,body,stream⟩:=DFTModelSavingNativeBilledWholeSchedule.execution
    n B T U A F H q rest stack depth stackTop reserve K cost x Complex.I h s s0 f f0 childIH cap
      geometry same pc parent metadata printed data data0 unitPointer unitPrinted mainEnd unitEnd
      stackEnd unitAbove floorUnit floorWork constants bound
  obtain ⟨u,u0,final,final0,result,work⟩:=finish n B T U A F H q rest stack depth stackTop reserve K prefixTicks
    cost x h s s0 f f0 t t0 first g g0 body stream geometry metadata cap positive
  exact ⟨u,u0,first+(4*(q*m)+W*UniformBinarySpectatorCMachine.arrayCost (q*m+rest) (q*m)+20),
    final,final0,result,work⟩

end
end ExactFourierCircuits.DFTModelSavingNativeBilledPrintedBody

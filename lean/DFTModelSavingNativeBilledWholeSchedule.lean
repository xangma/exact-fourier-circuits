import DFTModelSavingNativeWholeSchedule
import DFTModelSavingNativeBilledCore
import DFTModelSavingChronologyWork
import DFTModelSavingClosedBody
import DFTModelSavingCostFactorPadding
import DFTModelSavingNativePaddingStepBilled
import UniformRecursiveWholeSchedule

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeBilledWholeSchedule
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine
open UniformNativeScheduleSemantics UniformRecursiveTypedBody UniformRecursiveCoreSchedule
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursiveResidualEdge (Parent)
open UniformNativeHandlerSemantics (arrayValues)
open DFTModelClockControl DFTModelAffine DFTModelAdmissibilityControl
open DFTModelRecursiveScalarSource (paired)
namespace P
export UniformRecursiveSavingProgram (program address seedLength unitLength unitRecord)
end P
noncomputable section
attribute [local irreducible] P.program DFTModelSavingRecords.dispatch coreInstructions instructions
  DFTModelSavingNativeSequence.typedFold DFTModelSavingChronology.recordStep
  DFTModelSavingRecords.stream DFTModelCacheRecords.seed

/-- The actual printed core and final padding execute in order. Both source
runs and the single paired typed stream retain the exact returned flags. -/
theorem execution (n B T U A F H q rest stack depth stackTop reserve K : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (I : ℂ) (h : Handler ChildPort)
    (s s0 : State) (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (childIH : DFTModelSavingResidualNativeGroup.BilledPairSmallerBodies
      (q*m+rest) n B reserve stack stackTop K K cost x I h)
    (cap : DFTModelSavingCost.nativeWorkFactor≤K)
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
    ∃u u0 time g g0,DFTModelSavingNativeWholeSchedule.Result n B T U A F H q rest stack depth stackTop cost x I h s s0 u u0 time f f0 g g0 ∧
      ((DFTModelSavingRecords.stream W).run h
        (rest,((run DFTModelCacheRecords.seed q).val,((q*m+rest,I),paired f f0)))).work≤K*time+12 := by
  have ph:PrintedRecords T ((coreInstructions.map (Instruction.record q))++[Instruction.record q .padding]) s:=by
    have eq:coreInstructions.map (Instruction.record q)++[Instruction.record q .padding]=scheduleRecords q:=by
      rw [←records_actual,instructions_core,List.map_append,List.map_cons,List.map_nil]
    rw [eq];exact printed
  obtain ⟨coreBank,padBank⟩:=printedRecords_append T _ _ s ph
  have len:=core_length q
  obtain ⟨t,t0,first,g,g0,core⟩:=DFTModelSavingNativeBilledCore.run_records n B (T+P.seedLength) A F q rest
    stack depth stackTop reserve K cost x I h coreInstructions childIH cap geometry core_noPadding mainEnd
    T s s0 f f0 same pc parent metadata coreBank data data0 (by omega) stackEnd constants bound
  have storedMeta:t.natHeap (F-1)=some (T+P.seedLength):=
    (core.frame.metadata geometry.low stackEnd (by omega)).trans metadata
  have ptr:t.natHeap (F-2)=some U:=by
    rw [core.frame.natHeap _ (by have h:=geometry.low;omega) (Or.inr (by omega)) (by have h:=geometry.low;omega)]
    exact unitPointer
  have bank:Printed U (P.unitRecord.withColumns q).data t:=by
    intro j hj
    have unchanged:(P.unitRecord.withColumns q).data.length=P.unitRecord.data.length:=by
      simp only [Record.data_length,Record.withColumns]
    have hlen:(P.unitRecord.withColumns q).data.length=P.unitLength:=
      unchanged.trans UniformRecursiveSavingProgram.unitRecord_length
    rw [hlen] at hj
    rw [core.frame.natHeap _ (by omega) (Or.inr (by omega)) (by omega)]
    exact unitPrinted j (by rwa [hlen])
  have pad:Printed (T+(serialize (coreInstructions.map (Instruction.record q))).length)
      (Instruction.record q .padding).data t:=by
    intro j hj
    rw [padding_length] at hj
    rw [core.frame.natHeap _ (by omega) (Or.inr (by omega)) (by omega)]
    exact padBank.1 j (by rwa [padding_length])
  obtain ⟨u,u0,last,g',g0',tail,tailWork⟩:=DFTModelSavingNativePaddingStep.billed_execution
    n B (T+(serialize (coreInstructions.map (Instruction.record q))).length) (T+P.seedLength) U A F q rest
    stack depth stackTop reserve K cost x I h childIH geometry t t0 g g0 core.matched core.pc core.parent storedMeta
    (by omega) pad ptr bank core.data core.data0 (by have fb:=geometry.poolEnd;rw [padding_length];omega)
    unitEnd unitAbove core.constants core.actual.final_bound
      ((DFTModelSavingCost.factor_direction rest geometry.remainder).trans cap)
      (DFTModelSavingCost.factor_padding_control.trans cap)
  refine ⟨u,u0,first+last,g',g0',?_,?_⟩
  · refine {
      actual:=core.actual.trans tail.actual,baseline:=core.baseline.trans tail.baseline,
      matched:=tail.matched,pc:=tail.pc,pc0:=tail.pc0,parent:=?_,parent0:=?_,data:=tail.data,data0:=tail.data0,
      values:=?_,values0:=?_,metadata:=?_,unitPointer:=?_,natHeap:=?_,natHeap0:=?_,scalarHeap:=?_,scalarHeap0:=?_,
      roots:=tail.frame.roots.trans core.frame.roots,roots0:=tail.frame0.roots.trans core.frame0.roots,
      outputs:=tail.frame.outputs.trans core.frame.outputs,outputs0:=tail.frame0.outputs.trans core.frame0.outputs,
      constants:=tail.constants,constants0:=tail.constants0,
      time_bound:=Nat.add_le_add core.time_bound tail.time_bound,code:=?_}
    · simpa only [padding_length,Nat.add_assoc,len] using tail.parent
    · simpa only [padding_length,Nat.add_assoc,len] using tail.parent0
    · rw [instructions_core,UniformRecursiveWholeSchedule.interpret_append]
      change arrayValues q rest g'=(semantic q rest .padding).mulVec (interpret q rest coreInstructions (arrayValues q rest f))
      rw [←core.values];exact tail.values
    · rw [instructions_core,UniformRecursiveWholeSchedule.interpret_append]
      change arrayValues q rest g0'=(semantic q rest .padding).mulVec (interpret q rest coreInstructions (arrayValues q rest f0))
      rw [←core.values0];exact tail.values0
    · exact tail.frame.endPointer.trans (core.frame.metadata geometry.low stackEnd (by omega))
    · exact tail.frame.unitPointer.trans
        (core.frame.natHeap _ (by have h:=geometry.low;omega) (Or.inr (by omega)) (by have h:=geometry.low;omega))
    · intro z hz away
      exact (tail.frame.natHeap z (by omega) away (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
        (core.frame.natHeap z (by omega) away (by omega))
    · intro z hz away
      exact (tail.frame0.natHeap z (by omega) away (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
        (core.frame0.natHeap z (by omega) away (by omega))
    · intro z hz away;exact (tail.frame.scalarHeap z hz away).trans (core.frame.scalarHeap z hz away)
    · intro z hz away;exact (tail.frame0.scalarHeap z hz away).trans (core.frame0.scalarHeap z hz away)
    · exact (congrArg (fun is=>DFTModelSavingNativeSequence.typedFold q rest I h is f f0)
        instructions_core).trans
          (DFTModelSavingNativeWholeSchedule.typedFold_append_padding q rest I h coreInstructions f f0 g g0 g' g0' core.code tail.code)
  · have coreCode : DFTModelSavingChronology.recordFold W rest h
        (coreInstructions.map (Instruction.record q)) ((q*m+rest,I),paired f f0)=
          ((q*m+rest,I),paired g g0) := by
      rw [DFTModelSavingClosedBody.recordFold_map]
      have before:=core.code
      unfold DFTModelSavingNativeSequence.typedFold at before
      exact before
    rw [DFTModelCacheRecords.seed_value,←records_actual,instructions_core,
      List.map_append,List.map_cons,List.map_nil,
      DFTModelSavingChronologyWork.stream_snoc_work,coreCode]
    have a:=core.work
    have b:=tailWork
    rw [Nat.mul_add]
    omega

end
end ExactFourierCircuits.DFTModelSavingNativeBilledWholeSchedule

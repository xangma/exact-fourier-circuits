import DFTModelSavingNativeCore
import DFTModelSavingNativePaddingStep
import UniformRecursiveWholeSchedule

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeWholeSchedule
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

lemma typedFold_append_padding (q rest : ℕ) (I : ℂ) (h : Handler ChildPort)
    (is : List TypedInstruction) (f f0 g g0 g' g0' : Fin W→Fin (2^(q*m+rest))→Scalar)
    (before : DFTModelSavingNativeSequence.typedFold q rest I h is f f0=((q*m+rest,I),paired g g0))
    (after : DFTModelSavingChronology.recordStep W rest h (Instruction.record q .padding)
      ((q*m+rest,I),paired g g0)=((q*m+rest,I),paired g' g0')) :
    DFTModelSavingNativeSequence.typedFold q rest I h (is++[.padding]) f f0=
      ((q*m+rest,I),paired g' g0') := by
  unfold DFTModelSavingNativeSequence.typedFold at before ⊢
  rw [List.foldl_append,List.foldl_cons,List.foldl_nil,before]
  exact after


structure Result (n B T U A F H q rest stack depth stackTop : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (I : ℂ) (h : Handler ChildPort)
    (s s0 u u0 : State) (time : ℕ)
    (f f0 g g0 : Fin W→Fin (2^(q*m+rest))→Scalar) : Prop where
  actual : BoundedRuns P.program n x B s time u
  baseline : BoundedRuns P.program n (fun _=>0) B s0 time u0
  matched : StateMatch u u0
  pc : u.pc=P.address .loop
  pc0 : u0.pc=P.address .loop
  parent : Parent (q*m+rest) q A F (T+P.seedLength) rest stack depth u
  parent0 : Parent (q*m+rest) q A F (T+P.seedLength) rest stack depth u0
  data : Present A W (2^(q*m+rest)) g u
  data0 : Present A W (2^(q*m+rest)) g0 u0
  values : arrayValues q rest g=interpret q rest instructions (arrayValues q rest f)
  values0 : arrayValues q rest g0=interpret q rest instructions (arrayValues q rest f0)
  metadata : u.natHeap (F-1)=s.natHeap (F-1)
  unitPointer : u.natHeap (F-2)=s.natHeap (F-2)
  natHeap : ∀z,z<H→(z<stack+34*depth∨stackTop≤z)→u.natHeap z=s.natHeap z
  natHeap0 : ∀z,z<H→(z<stack+34*depth∨stackTop≤z)→u0.natHeap z=s0.natHeap z
  scalarHeap : ∀z,z<F→(z<A∨A+W*2^(q*m+rest)≤z)→u.scalarHeap z=s.scalarHeap z
  scalarHeap0 : ∀z,z<F→(z<A∨A+W*2^(q*m+rest)≤z)→u0.scalarHeap z=s0.scalarHeap z
  roots : u.rootOrders=s.rootOrders
  roots0 : u0.rootOrders=s0.rootOrders
  outputs : u.outputs=s.outputs
  outputs0 : u0.outputs=s0.outputs
  constants : UniformBinaryCStageMachine.Constants u
  constants0 : UniformBinaryCStageMachine.Constants u0
  time_bound : time≤(coreInstructions.map (ticks q rest cost)).sum+
    (73+(W-actualRoles)*(64+m*UniformRecursiveResidualDirectionLoop.directionCost q (m-1) rest 32 cost))
  code : DFTModelSavingNativeSequence.typedFold q rest I h instructions f f0=((q*m+rest,I),paired g g0)

/-- The actual printed core and final padding execute in order. Both source
runs and the single paired typed stream retain the exact returned flags. -/
theorem execution (n B T U A F H q rest stack depth stackTop reserve : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (I : ℂ) (h : Handler ChildPort)
    (s s0 : State) (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (childIH : DFTModelSavingResidualNativeGroup.PairSmallerBodies
      (q*m+rest) n B reserve stack stackTop cost x I h)
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
    ∃u u0 time g g0,Result n B T U A F H q rest stack depth stackTop cost x I h s s0 u u0 time f f0 g g0 := by
  have ph:PrintedRecords T ((coreInstructions.map (Instruction.record q))++[Instruction.record q .padding]) s:=by
    have eq:coreInstructions.map (Instruction.record q)++[Instruction.record q .padding]=scheduleRecords q:=by
      rw [←records_actual,instructions_core,List.map_append,List.map_cons,List.map_nil]
    rw [eq];exact printed
  obtain ⟨coreBank,padBank⟩:=printedRecords_append T _ _ s ph
  have len:=core_length q
  obtain ⟨t,t0,first,g,g0,core⟩:=DFTModelSavingNativeCore.run_records n B (T+P.seedLength) A F q rest
    stack depth stackTop reserve cost x I h coreInstructions childIH geometry core_noPadding mainEnd
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
  obtain ⟨u,u0,last,g',g0',tail⟩:=DFTModelSavingNativePaddingStep.execution
    n B (T+(serialize (coreInstructions.map (Instruction.record q))).length) (T+P.seedLength) U A F q rest
    stack depth stackTop reserve cost x I h childIH geometry t t0 g g0 core.matched core.pc core.parent storedMeta
    (by omega) pad ptr bank core.data core.data0 (by have fb:=geometry.poolEnd;rw [padding_length];omega)
    unitEnd unitAbove core.constants core.actual.final_bound
  refine ⟨u,u0,first+last,g',g0',?_⟩
  refine {
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
        (typedFold_append_padding q rest I h coreInstructions f f0 g g0 g' g0' core.code tail.code)

end
end ExactFourierCircuits.DFTModelSavingNativeWholeSchedule

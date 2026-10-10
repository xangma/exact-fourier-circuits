import DFTModelSavingNativeSequence
import DFTModelSavingCostRecords

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeBilledSequence
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine
open UniformNativeScheduleSemantics UniformRecursiveTypedBody
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursiveResidualEdge (Parent)
open DFTModelClockControl DFTModelAffine DFTModelAdmissibilityControl
open DFTModelRecursiveScalarSource (paired)
open DFTModelSavingNativeSequence
namespace P
export UniformRecursiveSavingProgram (program address)
end P
noncomputable section
attribute [local irreducible] P.program DFTModelSavingRecords.dispatch DFTModelSavingRecords.stream

lemma steps_shift_work {α : Type} (x : α) (f : ℕ→α→Bill α) (n : ℕ) :
    (Bill.steps x f (n+1)).work=(f 0 x).work+
      (Bill.steps (f 0 x).val (fun i=>f (i+1)) n).work+1 := by
  induction n with
  | zero=>simp [Bill.steps,Bill.one,Bill.pass,Bill.pay,Nat.add_comm]
  | succ n ih=>
    change (Bill.steps x f (n+1)).work+
      (f (n+1) (Bill.steps x f (n+1)).val).work+1=_
    rw [ih,DFTModelSavingChronology.steps_succ_start]
    change _=(f 0 x).work+
      ((Bill.steps (f 0 x).val (fun i=>f (i+1)) n).work+
        (f (n+1) (Bill.steps (f 0 x).val (fun i=>f (i+1)) n).val).work+1)+1
    omega

/-- The twenty-two control steps are charged for each actual chronological
record; the stream's twelve initial steps are charged once. -/
lemma stream_cons_work (R rest : ℕ) (h : Handler ChildPort) (r : Record)
    (rs : List Record) (node : Node.T) :
    ((DFTModelSavingRecords.stream R).run h
      (rest,(DFTModelCacheRecords.recordTape (r::rs),node))).work=
    ((DFTModelSavingRecords.dispatch R).run h
      (rest,(DFTModelCacheRecords.dataTape r.data,node))).work+
    ((DFTModelSavingRecords.stream R).run h
      (rest,(DFTModelCacheRecords.recordTape rs,
        DFTModelSavingChronology.recordStep R rest h r node))).work+22 := by
  rw [DFTModelSavingCost.stream_run,DFTModelSavingCost.stream_run]
  dsimp only [Bill.pay,DFTModelSavingCost.recordSteps]
  change (Bill.steps node _ (rs.length+1)).work+_= _
  rw [steps_shift_work,DFTModelSavingChronology.recordTape_head]
  have tail : (fun i current=>(DFTModelSavingRecords.dispatch R).run h
      (rest,((DFTModelCacheRecords.recordTape (r::rs)).look (i+1) (Tape.empty ℕ),current)))=
      (fun i current=>(DFTModelSavingRecords.dispatch R).run h
        (rest,((DFTModelCacheRecords.recordTape rs).look i (Tape.empty ℕ),current))) := by
    funext i current
    rw [DFTModelSavingChronology.recordTape_tail]
  rw [tail]
  have firstLen:(DFTModelCacheRecords.recordTape (r::rs)).len=rs.length+1:=rfl
  have tailLen:(DFTModelCacheRecords.recordTape rs).len=rs.length:=rfl
  rw [firstLen,tailLen]
  dsimp only [DFTModelSavingChronology.recordStep]
  omega

structure StepResult (n B T A F q rest stack depth stackTop K : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (I : ℂ) (h : Handler ChildPort)
    (i : TypedInstruction) (s s0 : State) (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (u u0 : State) (time : ℕ) (g g0 : Fin W→Fin (2^(q*m+rest))→Scalar) : Prop
    extends DFTModelSavingNativeSequence.StepResult n B T A F q rest stack depth stackTop
      cost x I h i s s0 f f0 u u0 time g g0 where
  work : ((DFTModelSavingRecords.dispatch W).run h
    (rest,(DFTModelCacheRecords.dataTape (Instruction.record q i).data,
      ((q*m+rest,I),paired f f0)))).work+22≤K*time

structure SequenceResult (n B T A F q rest stack depth stackTop K : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (I : ℂ) (h : Handler ChildPort)
    (is : List TypedInstruction) (s s0 : State) (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (u u0 : State) (time : ℕ) (g g0 : Fin W→Fin (2^(q*m+rest))→Scalar) : Prop
    extends DFTModelSavingNativeSequence.SequenceResult n B T A F q rest stack depth stackTop
      cost x I h is s s0 f f0 u u0 time g g0 where
  work : ((DFTModelSavingRecords.stream W).run h
    (rest,(DFTModelCacheRecords.recordTape (is.map (Instruction.record q)),
      ((q*m+rest,I),paired f f0)))).work≤K*time+12

/-- Actual source execution and its billing are composed together. In
particular an upper bound on source ticks cannot replace the witnessed ticks
in this induction. The final opcode family discharges the internal steps. -/
theorem run_records (n B tapeEnd A F q rest stack depth stackTop reserve K : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (I : ℂ) (h : Handler ChildPort) (is : List TypedInstruction)
    (geometry : Geometry B A F q rest stack depth stackTop reserve)
    (mainEnd : tapeEnd≤F-6)
    (steps : ∀i∈is,∀(T : ℕ)(s s0 : State)(f f0 : Fin W→Fin (2^(q*m+rest))→Scalar),
      StateMatch s s0→s.pc=P.address .loop→Parent (q*m+rest) q A F T rest stack depth s→
      s.natHeap (F-1)=some tapeEnd→T<tapeEnd→Printed T (Instruction.record q i).data s→
      Present A W (2^(q*m+rest)) f s→Present A W (2^(q*m+rest)) f0 s0→
      T+(Instruction.record q i).data.length≤F-6→stackTop≤T→
      UniformBinaryCStageMachine.Constants s→WordBound B s→
      ∃u u0 time g g0,StepResult n B T A F q rest stack depth stackTop K cost x I h i s s0 f f0 u u0 time g g0) :
    ∀(T : ℕ)(s s0 : State)(f f0 : Fin W→Fin (2^(q*m+rest))→Scalar),
      StateMatch s s0→s.pc=P.address .loop→Parent (q*m+rest) q A F T rest stack depth s→
      s.natHeap (F-1)=some tapeEnd→PrintedRecords T (is.map (Instruction.record q)) s→
      Present A W (2^(q*m+rest)) f s→Present A W (2^(q*m+rest)) f0 s0→
      T+(serialize (is.map (Instruction.record q))).length≤tapeEnd→stackTop≤T→
      UniformBinaryCStageMachine.Constants s→WordBound B s→
      ∃u u0 time g g0,SequenceResult n B T A F q rest stack depth stackTop K cost x I h is s s0 f f0 u u0 time g g0 := by
  induction is with
  | nil=>
    intro T s s0 f f0 same pc parent metadata printed data data0 endBound stackEnd constants bound
    obtain ⟨u,u0,time,g,g0,result⟩:=DFTModelSavingNativeSequence.run_records
      n B tapeEnd A F q rest stack depth stackTop reserve cost x I h [] geometry mainEnd
      (by intro i hi;cases hi) T s s0 f f0 same pc parent metadata printed data data0 endBound stackEnd constants bound
    refine ⟨u,u0,time,g,g0,result,?_⟩
    rw [DFTModelSavingCost.stream_run]
    change 12≤K*time+12
    omega
  | cons i is ih=>
    intro T s s0 f f0 same pc parent metadata printed data data0 endBound stackEnd constants bound
    have lengths:(serialize ((i::is).map (Instruction.record q))).length=
      (Instruction.record q i).data.length+(serialize (is.map (Instruction.record q))).length :=
      serialized_cons _ _
    have split : Printed T (Instruction.record q i).data s ∧
      PrintedRecords (T+(Instruction.record q i).data.length) (is.map (Instruction.record q)) s:=printed
    have endSingle:T+(Instruction.record q i).data.length≤F-6:=by rw [lengths] at endBound;omega
    have live:T<tapeEnd:=by have pos:=record_positive (Instruction.record q i);rw [lengths] at endBound;omega
    obtain ⟨t,t0,first,g,g0,one⟩:=steps i (by simp) T s s0 f f0 same pc parent metadata live split.1 data data0
      endSingle stackEnd constants bound
    have nextBank:=printedRecords_transport one.frame _ split.2 (by omega)
      (show T+(Instruction.record q i).data.length+(serialize (is.map (Instruction.record q))).length≤F-6 by
        rw [lengths] at endBound;omega)
    have nextMetadata:t.natHeap (F-1)=some tapeEnd:=
      (one.frame.metadata geometry.low stackEnd (by omega)).trans metadata
    obtain ⟨u,u0,remaining,g',g0',tail⟩:=ih
      (by intro j hj;exact steps j (by simp [hj]))
      (T+(Instruction.record q i).data.length) t t0 g g0 one.matched one.pc one.parent nextMetadata nextBank
      one.data one.data0 (by rw [lengths] at endBound;omega) (by omega) one.constants one.actual.final_bound
    refine ⟨u,u0,first+remaining,g',g0',?_⟩
    refine ⟨?_,?_⟩
    · refine ⟨one.actual.trans tail.actual,one.baseline.trans tail.baseline,tail.matched,tail.pc,tail.pc0,
        ?_,?_,tail.data,tail.data0,?_,?_,one.frame.trans tail.frame,one.frame0.trans tail.frame0,
        tail.constants,tail.constants0,?_,?_⟩
      · simpa only [lengths,Nat.add_assoc] using tail.parent
      · simpa only [lengths,Nat.add_assoc] using tail.parent0
      · change UniformNativeHandlerSemantics.arrayValues q rest g'=
          interpret q rest is ((semantic q rest i).mulVec (UniformNativeHandlerSemantics.arrayValues q rest f))
        rw [←one.values];exact tail.values
      · change UniformNativeHandlerSemantics.arrayValues q rest g0'=
          interpret q rest is ((semantic q rest i).mulVec (UniformNativeHandlerSemantics.arrayValues q rest f0))
        rw [←one.values0];exact tail.values0
      · simp only [List.map_cons,List.sum_cons]
        exact Nat.add_le_add one.time_bound tail.time_bound
      · change is.foldl _ (DFTModelSavingChronology.recordStep W rest h
          (Instruction.record q i) ((q*m+rest,I),paired f f0))=_
        rw [one.code]
        exact tail.code
    · rw [List.map_cons,stream_cons_work,one.code]
      have a:=one.work
      have b:=tail.work
      rw [Nat.mul_add]
      omega

end
end ExactFourierCircuits.DFTModelSavingNativeBilledSequence

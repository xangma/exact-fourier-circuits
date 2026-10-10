import DFTModelSavingClosedBody
import DFTModelSavingNativeMarker
import DFTModelSavingNativeY

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeSequence
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine
open UniformNativeScheduleSemantics UniformRecursiveTypedBody
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursiveResidualEdge (Parent)
open UniformNativeHandlerSemantics (arrayValues)
open DFTModelClockControl DFTModelAffine DFTModelAdmissibilityControl
open DFTModelRecursiveScalarSource (paired)
namespace P
export UniformRecursiveSavingProgram (program address)
end P
noncomputable section
attribute [local irreducible] P.program DFTModelSavingRecords.dispatch

def typedFold (q rest : ℕ) (I : ℂ) (h : Handler ChildPort)
    (is : List TypedInstruction) (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar) : Node.T :=
  is.foldl (fun current i=>DFTModelSavingChronology.recordStep W rest h
    (Instruction.record q i) current) ((q*m+rest,I),paired f f0)

/-- Exact source outputs, including flags, for one real typed record. The
internal child hypothesis used to construct this result is kept outside it. -/
structure StepResult (n B T A F q rest stack depth stackTop : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (I : ℂ) (h : Handler ChildPort)
    (i : TypedInstruction) (s s0 : State) (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (u u0 : State) (time : ℕ) (g g0 : Fin W→Fin (2^(q*m+rest))→Scalar) : Prop where
  actual : BoundedRuns P.program n x B s time u
  baseline : BoundedRuns P.program n (fun _=>0) B s0 time u0
  matched : StateMatch u u0
  pc : u.pc=P.address .loop
  pc0 : u0.pc=P.address .loop
  parent : Parent (q*m+rest) q A F (T+(Instruction.record q i).data.length) rest stack depth u
  parent0 : Parent (q*m+rest) q A F (T+(Instruction.record q i).data.length) rest stack depth u0
  data : Present A W (2^(q*m+rest)) g u
  data0 : Present A W (2^(q*m+rest)) g0 u0
  values : arrayValues q rest g=(semantic q rest i).mulVec (arrayValues q rest f)
  values0 : arrayValues q rest g0=(semantic q rest i).mulVec (arrayValues q rest f0)
  frame : Frame A F q rest stack depth stackTop s u
  frame0 : Frame A F q rest stack depth stackTop s0 u0
  constants : UniformBinaryCStageMachine.Constants u
  constants0 : UniformBinaryCStageMachine.Constants u0
  time_bound : time≤ticks q rest cost i
  code : DFTModelSavingChronology.recordStep W rest h (Instruction.record q i)
    ((q*m+rest,I),paired f f0)=((q*m+rest,I),paired g g0)

structure SequenceResult (n B T A F q rest stack depth stackTop : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (I : ℂ) (h : Handler ChildPort)
    (is : List TypedInstruction) (s s0 : State) (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (u u0 : State) (time : ℕ) (g g0 : Fin W→Fin (2^(q*m+rest))→Scalar) : Prop where
  actual : BoundedRuns P.program n x B s time u
  baseline : BoundedRuns P.program n (fun _=>0) B s0 time u0
  matched : StateMatch u u0
  pc : u.pc=P.address .loop
  pc0 : u0.pc=P.address .loop
  parent : Parent (q*m+rest) q A F (T+(serialize (is.map (Instruction.record q))).length) rest stack depth u
  parent0 : Parent (q*m+rest) q A F (T+(serialize (is.map (Instruction.record q))).length) rest stack depth u0
  data : Present A W (2^(q*m+rest)) g u
  data0 : Present A W (2^(q*m+rest)) g0 u0
  values : arrayValues q rest g=interpret q rest is (arrayValues q rest f)
  values0 : arrayValues q rest g0=interpret q rest is (arrayValues q rest f0)
  frame : Frame A F q rest stack depth stackTop s u
  frame0 : Frame A F q rest stack depth stackTop s0 u0
  constants : UniformBinaryCStageMachine.Constants u
  constants0 : UniformBinaryCStageMachine.Constants u0
  time_bound : time≤(is.map (ticks q rest cost)).sum
  code : typedFold q rest I h is f f0=((q*m+rest,I),paired g g0)

/-- Internal chronological induction. Its step obligation is a genuine paired
execution of this same fixed RAM program, never a semantic callback. Concrete
opcode proofs discharge that obligation before the complete compiler theorem. -/
theorem run_records (n B tapeEnd A F q rest stack depth stackTop reserve : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (I : ℂ) (h : Handler ChildPort) (is : List TypedInstruction)
    (geometry : Geometry B A F q rest stack depth stackTop reserve)
    (mainEnd : tapeEnd≤F-6)
    (steps : ∀i∈is,∀(T : ℕ)(s s0 : State)(f f0 : Fin W→Fin (2^(q*m+rest))→Scalar),
      StateMatch s s0→s.pc=P.address .loop→Parent (q*m+rest) q A F T rest stack depth s→
      s.natHeap (F-1)=some tapeEnd→T<tapeEnd→Printed T (Instruction.record q i).data s→
      Present A W (2^(q*m+rest)) f s→Present A W (2^(q*m+rest)) f0 s0→
      T+(Instruction.record q i).data.length≤F-6→stackTop≤T→
      UniformBinaryCStageMachine.Constants s→WordBound B s→
      ∃u u0 time g g0,StepResult n B T A F q rest stack depth stackTop cost x I h i s s0 f f0 u u0 time g g0) :
    ∀(T : ℕ)(s s0 : State)(f f0 : Fin W→Fin (2^(q*m+rest))→Scalar),
      StateMatch s s0→s.pc=P.address .loop→Parent (q*m+rest) q A F T rest stack depth s→
      s.natHeap (F-1)=some tapeEnd→PrintedRecords T (is.map (Instruction.record q)) s→
      Present A W (2^(q*m+rest)) f s→Present A W (2^(q*m+rest)) f0 s0→
      T+(serialize (is.map (Instruction.record q))).length≤tapeEnd→stackTop≤T→
      UniformBinaryCStageMachine.Constants s→WordBound B s→
      ∃u u0 time g g0,SequenceResult n B T A F q rest stack depth stackTop cost x I h is s s0 f f0 u u0 time g g0 := by
  induction is with
  | nil=>
    intro T s s0 f f0 same pc parent metadata printed data data0 endBound stackEnd constants bound
    have parent0:=DFTModelSavingNativeExchange.parent_match same parent
    refine ⟨s,s0,0,f,f0,?_⟩
    exact ⟨.refl bound,.refl (same.wordBound bound),same,pc,same.pc.trans pc,
      by simpa only [List.map_nil,serialize,List.flatten_nil,List.length_nil,Nat.add_zero] using parent,
      by simpa only [List.map_nil,serialize,List.flatten_nil,List.length_nil,Nat.add_zero] using parent0,
      data,data0,rfl,rfl,Frame.refl _ _ _ _ _ _ _ _,Frame.refl _ _ _ _ _ _ _ _,
      constants,DFTModelSavingNativeExchange.constants_match same constants,le_rfl,rfl⟩
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
    refine ⟨one.actual.trans tail.actual,one.baseline.trans tail.baseline,tail.matched,tail.pc,tail.pc0,
      ?_,?_,tail.data,tail.data0,?_,?_,one.frame.trans tail.frame,one.frame0.trans tail.frame0,
      tail.constants,tail.constants0,?_,?_⟩
    · simpa only [lengths,Nat.add_assoc] using tail.parent
    · simpa only [lengths,Nat.add_assoc] using tail.parent0
    · change arrayValues q rest g'=interpret q rest is ((semantic q rest i).mulVec (arrayValues q rest f))
      rw [←one.values];exact tail.values
    · change arrayValues q rest g0'=interpret q rest is ((semantic q rest i).mulVec (arrayValues q rest f0))
      rw [←one.values0];exact tail.values0
    · simp only [List.map_cons,List.sum_cons]
      exact Nat.add_le_add one.time_bound tail.time_bound
    · change is.foldl _ (DFTModelSavingChronology.recordStep W rest h
        (Instruction.record q i) ((q*m+rest,I),paired f f0))=_
      rw [one.code]
      exact tail.code

end
end ExactFourierCircuits.DFTModelSavingNativeSequence

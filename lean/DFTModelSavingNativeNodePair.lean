import DFTModelSavingNativeNode
import DFTModelSavingNativeEntry

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSavingNativeNode
open UniformMachine BinaryFrames UniformFixedNetwork UniformFixedNetworkScheduleMachine
open UniformRecursiveTypedBody UniformRecursiveNodePreparation
open UniformRecursiveResidualEdge (Parent)
open UniformFixedNetworkShearChildMachine (Present)
open DFTModelAdmissibilityControl DFTModelSavingNativeControl
noncomputable section

attribute [local irreducible] P.program P.seedLength P.unitLength P.unitRecord
  P.threshold P.seedPrinterLength P.unitPrinterLength P.size

/-- Both actual source runs generate their own seed and unit tables, retain
their entire physical input bank, and reach the same next source instruction.
The ready tables are produced within the charged execution. -/
theorem paired (n B F M l A q rest stack depth stackTop reserve : ℕ)
    (x : Fin n→ℂ) (s s0 : State) (same : StateMatch s s0)
    (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (eqM : M=P.seedLength) (eql : l=P.unitLength)
    (geometry : Geometry B A (workBase F M l) q rest stack depth stackTop reserve)
    (large : P.threshold≤q*m+rest) (thresholdBound : P.threshold≤B)
    (pc : s.pc=P.address .readyEntry) (bits : s.natReg 4120=q*m+rest)
    (base : s.natReg 4121=A) (volume : s.natReg 4122=2^(q*m+rest))
    (frontier : s.natReg 4123=F) (nativeBase : s.natReg 3300=A)
    (nativeBits : s.natReg 5300=q*m+rest) (sp : s.natReg 4150=stack)
    (dp : s.natReg 4151=depth) (one : s.natReg 4153=1)
    (data : Present A W (2^(q*m+rest)) f s)
    (baseline : Present A W (2^(q*m+rest)) f0 s0)
    (constants : UniformBinaryCStageMachine.Constants s)
    (literals : literalCap (serialize baseSchedule)≤B) (bound : WordBound B s) :
    ∃t t0,
      BoundedRuns P.program n x B s
        (9+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady)) t ∧
      BoundedRuns P.program n (fun _=>0) B s0
        (9+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady)) t0 ∧
      StateMatch t t0 ∧ t.pc=P.address .loop ∧ t0.pc=P.address .loop ∧
      Parent (q*m+rest) q A (workBase F M l) F rest stack depth t ∧
      Parent (q*m+rest) q A (workBase F M l) F rest stack depth t0 ∧
      t.natHeap (workBase F M l-2)=some (unitBase F M) ∧
      t.natHeap (workBase F M l-1)=some (unitBase F M) ∧
      t0.natHeap (workBase F M l-2)=some (unitBase F M) ∧
      t0.natHeap (workBase F M l-1)=some (unitBase F M) ∧
      PrintedRecords F (scheduleRecords q) t ∧
      PrintedRecords F (scheduleRecords q) t0 ∧
      Printed (unitBase F M) (P.unitRecord.withColumns q).data t ∧
      Printed (unitBase F M) (P.unitRecord.withColumns q).data t0 ∧
      Present A W (2^(q*m+rest)) f t ∧ Present A W (2^(q*m+rest)) f0 t0 ∧
      UniformBinaryCStageMachine.Constants t ∧UniformBinaryCStageMachine.Constants t0 ∧
      Frame F (workBase F M l) s t ∧Frame F (workBase F M l) s0 t0 := by
  obtain ⟨t,actual,tp,parent,ptr2,ptr1,main,unitBank,_,frame⟩:=
    single n B F M l A q rest stack depth stackTop reserve x s eqM eql geometry
      large thresholdBound pc bits base volume frontier nativeBase nativeBits sp dp one literals bound
  obtain ⟨t0,zero,tp0,parent0,ptr20,ptr10,main0,unitBank0,_,frame0⟩:=
    single n B F M l A q rest stack depth stackTop reserve (fun _=>0) s0 eqM eql geometry
      large thresholdBound (same.pc.trans pc)
      (by rw [same.natReg];exact bits) (by rw [same.natReg];exact base)
      (by rw [same.natReg];exact volume) (by rw [same.natReg];exact frontier)
      (by rw [same.natReg];exact nativeBase) (by rw [same.natReg];exact nativeBits)
      (by rw [same.natReg];exact sp) (by rw [same.natReg];exact dp)
      (by rw [same.natReg];exact one) literals (same.wordBound bound)
  have dataT : Present A W (2^(q*m+rest)) f t := by
    intro i j;rw [frame.scalarHeap];exact data i j
  have data0 : Present A W (2^(q*m+rest)) f0 t0 := by
    intro i j;rw [frame0.scalarHeap];exact baseline i j
  have constantsT : UniformBinaryCStageMachine.Constants t := by
    unfold UniformBinaryCStageMachine.Constants at constants ⊢
    rw [frame.scalarHeap];exact constants
  have constants0 : UniformBinaryCStageMachine.Constants t0 := by
    have c:=DFTModelSavingNativeEntry.constants_match same constants
    unfold UniformBinaryCStageMachine.Constants at c ⊢
    rw [frame0.scalarHeap];exact c
  exact ⟨t,t0,actual,zero,paired_runs actual zero same,tp,tp0,parent,parent0,
    ptr2,ptr1,ptr20,ptr10,main,main0,unitBank,unitBank0,dataT,data0,
    constantsT,constants0,frame,frame0⟩

end
end ExactFourierCircuits.DFTModelSavingNativeNode

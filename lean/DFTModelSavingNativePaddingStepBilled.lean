import DFTModelSavingNativePaddingStep
import DFTModelSavingNativePaddingExecutionBilledConcrete

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSavingNativePaddingStep
open UniformMachine DFTModelAdmissibilityControl
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl UniformFixedNetwork UniformNativeScheduleSemantics UniformRecursiveTypedBody
open UniformFixedNetworkScheduleMachine (Printed)
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursiveResidualEdge (Parent)
open UniformNativeHandlerSemantics (arrayValues)
noncomputable section
attribute [local irreducible] P.program DFTModelSavingCost.unitAllowance DFTModelSavingRecords.dispatch

/-- Opcode five is decoded by the fixed source machine and every ascending
padding role runs the same smaller child once on both affine channels. -/
theorem billed_execution (n B T tapeEnd U A F q rest stack depth stackTop reserve K : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (I : ℂ) (h : Handler DFTModelSavingRecords.Port)
    (childIH : DFTModelSavingResidualNativeGroup.BilledPairSmallerBodies
      (q*m+rest) n B reserve stack stackTop K K cost x I h)
    (geometry : Geometry B A F q rest stack depth stackTop reserve)
    (s s0 : State) (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (same : StateMatch s s0) (pc : s.pc=P.address .loop)
    (parent : Parent (q*m+rest) q A F T rest stack depth s)
    (metadata : s.natHeap (F-1)=some tapeEnd) (live : T<tapeEnd)
    (printed : Printed T (Instruction.record q .padding).data s)
    (unitPointer : s.natHeap (F-2)=some U)
    (unitPrinted : Printed U (P.unitRecord.withColumns q).data s)
    (data : Present A W (2^(q*m+rest)) f s) (data0 : Present A W (2^(q*m+rest)) f0 s0)
    (recordEnd : T+(Instruction.record q .padding).data.length ≤ B)
    (unitEnd : U+P.unitLength ≤ F-6) (unitAbove : stackTop ≤ U)
    (constants : UniformBinaryCStageMachine.Constants s) (bound : WordBound B s)
    (coefficient : 363*m+240*rest+1347+104*W≤K)
    (fixed : DFTModelSavingCost.unitAllowance+52≤K) :
    ∃u u0 time g g0,Result n B T U A F q rest stack depth stackTop cost x I h s s0 u u0 time f f0 g g0 ∧
      ((DFTModelSavingRecords.dispatch W).run h
        (rest,(DFTModelCacheRecords.dataTape (Instruction.record q .padding).data,
          ((q*m+rest,I),DFTModelRecursiveScalarSource.paired f f0)))).work+22≤K*time := by
  obtain ⟨t,control,tp,fields,_,saved,cf⟩:=UniformRecursiveRecordControl.read_dispatch_execution
    F T tapeEnd B n (Instruction.record q .padding) x s pc parent.frontier parent.cursor parent.one metadata live
      printed (UniformRecursivePaddingRecord.actual_good q) bound recordEnd geometry.width geometry.code
  have parent0:=source_parent_match same parent
  obtain ⟨t0,control0,_,_,_,_,cf0⟩:=UniformRecursiveRecordControl.read_dispatch_execution
    F T tapeEnd B n (Instruction.record q .padding) (fun _=>0) s0 (same.pc.trans pc)
      parent0.frontier parent0.cursor parent0.one (by rw [same.natHeap];exact metadata) live
      (DFTModelSavingNativePaddingControl.printed_match same printed)
      (UniformRecursivePaddingRecord.actual_good q) (same.wordBound bound) recordEnd geometry.width geometry.code
  have matched:=DFTModelSavingNativeControl.paired_runs control control0 same
  have fi:(⟨(Instruction.record q .padding).opcode,(UniformRecursivePaddingRecord.actual_good q).1⟩:Fin 7)=5:=Fin.ext (by rfl)
  have entered:t.pc=P.address .paddingInit:=UniformRecursivePaddingRecord.padding_pc t.pc
    (tp.trans (congrArg UniformRecursiveRecordControl.targets fi))
  have pp:=UniformRecursivePaddingRecord.padding_parent parent cf
  have pointer:t.natHeap (F-2)=some U:=by rw [cf.natHeap];exact unitPointer
  have bank:Printed U (P.unitRecord.withColumns q).data t:=by
    intro j hj;rw [cf.natHeap];exact unitPrinted j hj
  have dataT:Present A W (2^(q*m+rest)) f t:=by
    intro i z;rw [cf.scalarHeap];exact data i z
  have dataT0:Present A W (2^(q*m+rest)) f0 t0:=by
    intro i z;rw [cf0.scalarHeap];exact data0 i z
  have ct:UniformBinaryCStageMachine.Constants t:=by
    unfold UniformBinaryCStageMachine.Constants at constants ⊢
    rw [cf.scalarHeap];exact constants
  have dest:t.natReg 2854=UniformFixedNetworkScheduleMachine.actualRoles:=
    fields.dest.trans (UniformPaddingRecordProjections.dest q)
  have count:t.natReg 2855=W-UniformFixedNetworkScheduleMachine.actualRoles:=
    fields.source.trans (UniformPaddingRecordProjections.source q)
  have startBound:UniformFixedNetworkScheduleMachine.actualRoles ≤ W:=MasterBudget.seed_actual_padding
  have widthEq:(m-1)+1=ExplicitSeedBudget.m:=by norm_num [m,ExplicitSeedBudget.m]
  have m2:2 ≤ (m-1)+1:=by norm_num [m,ExplicitSeedBudget.m]
  have unitSize:U+(UniformRecursivePaddingRole.record (m-1)).data.length ≤ F-6:=by
    rw [UniformRecursivePaddingExecution.record_actual (m-1) widthEq,UniformRecursiveSavingProgram.unitRecord_length]
    exact unitEnd
  have rolesBound:W ≤ B:=by
    have pos:=Nat.two_pow_pos (q*m+rest)
    have aw:=geometry.arrayEnd
    have fb:=geometry.poolEnd
    nlinarith
  obtain ⟨u,u0,last,g,g0,prior,tail,tailWork⟩:=DFTModelSavingNativePaddingExecution.billed_concrete
    n B U W A F q (m-1) rest stack depth stackTop reserve
      (T+(Instruction.record q .padding).data.length) UniformFixedNetworkScheduleMachine.actualRoles K cost x I h
      childIH t t0 f f0 matched geometry.smaller entered pp saved dest count pointer
      (UniformRecursivePaddingExecution.printed_actual_in (m-1) q U widthEq t bank) dataT dataT0 startBound
      geometry.positive m2 geometry.remainder geometry.batchFit unitSize geometry.width geometry.arrayEnd geometry.poolEnd
      geometry.square geometry.low geometry.base geometry.stackRoom unitAbove geometry.childRoom rolesBound ct
      control.final_bound geometry.code widthEq (by norm_num [m,ExplicitSeedBudget.m]) rfl
      (by simpa only [widthEq,m,W,UniformBatching.width] using coefficient) fixed
  have pu:UniformRecursivePaddingFrames.Parent (q*m+rest) q A F rest stack depth u:=tail.parent
  have pu0:UniformRecursivePaddingFrames.Parent (q*m+rest) q A F rest stack depth u0:=tail.zeroParent
  have fullParent:Parent (q*m+rest) q A F (T+(Instruction.record q .padding).data.length) rest stack depth u:=
    ⟨tail.cursor,pu.nativeBase,pu.original,pu.bits,pu.volume,pu.frontier,pu.rest,pu.stack,pu.depth,pu.one,
      pu.nativeBits,pu.nativeRest,pu.table,pu.columns,pu.width⟩
  have fullParent0:Parent (q*m+rest) q A F (T+(Instruction.record q .padding).data.length) rest stack depth u0:=
    ⟨(congrFun tail.matched.natReg 2850).trans tail.cursor,pu0.nativeBase,pu0.original,pu0.bits,pu0.volume,pu0.frontier,
      pu0.rest,pu0.stack,pu0.depth,pu0.one,pu0.nativeBits,pu0.nativeRest,pu0.table,pu0.columns,pu0.width⟩
  have run:BoundedRuns P.program n x B s (52+last) u:=by
    convert control.trans tail.run using 1
    simp only [UniformFixedNetworkOpcodeMachine.headCost,
      UniformRecursiveRecordControl.dispatchCost,UniformPaddingRecordProjections.opcode]
    norm_num
  have run0:BoundedRuns P.program n (fun _=>0) B s0 (52+last) u0:=by
    convert control0.trans tail.zeroRun using 1
    simp only [UniformFixedNetworkOpcodeMachine.headCost,
      UniformRecursiveRecordControl.dispatchCost,UniformPaddingRecordProjections.opcode]
    norm_num
  refine ⟨u,u0,52+last,g,g0,?_⟩
  constructor
  · refine {
      actual:=run,baseline:=run0,matched:=tail.matched,pc:=tail.pc,pc0:=tail.matched.pc.trans tail.pc,
      parent:=fullParent,parent0:=fullParent0,data:=tail.present,data0:=tail.zeroPresent,
      values:=?_,values0:=?_,frame:=?_,frame0:=?_,constants:=tail.constants,constants0:=tail.zeroConstants,
      time_bound:=?_,code:=?_}
    · apply UniformRecursivePaddingSemantic.padding_values q rest
      exact tail.values
    · apply UniformRecursivePaddingSemantic.padding_values q rest
      exact tail.zeroValues
    · refine ⟨tail.endPointer.trans (congrFun cf.natHeap (F-1)),tail.unitPointer.trans (congrFun cf.natHeap (F-2)),?_,?_,
        tail.roots.trans cf.roots,tail.outputs.trans cf.outputs⟩
      · intro z hz away a b c d e f
        exact (tail.nat z hz away a b c d e f).trans (congrFun cf.natHeap z)
      · intro z hz away;exact (tail.scalar z hz away).trans (congrFun cf.scalarHeap z)
    · refine ⟨tail.zeroEndPointer.trans (congrFun cf0.natHeap (F-1)),tail.zeroUnitPointer.trans (congrFun cf0.natHeap (F-2)),?_,?_,
        tail.zeroRoots.trans cf0.roots,tail.zeroOutputs.trans cf0.outputs⟩
      · intro z hz away a b c d e f
        exact (tail.zeroNat z hz away a b c d e f).trans (congrFun cf0.natHeap z)
      · intro z hz away;exact (tail.zeroScalar z hz away).trans (congrFun cf0.scalarHeap z)
    · have time:=tail.time
      unfold UniformRecursivePaddingRole.roleCost at time
      change last ≤ (W-UniformFixedNetworkScheduleMachine.actualRoles)*
        (m*UniformRecursiveResidualDirectionLoop.directionCost q (m-1) rest 32 cost+58+6)+21 at time
      have eq:m*UniformRecursiveResidualDirectionLoop.directionCost q (m-1) rest 32 cost+58+6=
        64+m*UniformRecursiveResidualDirectionLoop.directionCost q (m-1) rest 32 cost:=by omega
      rw [eq] at time
      omega
    · rw [record_value]
      exact tail.value
  · have headers:=data_header (Instruction.record q .padding)
    have wh:=DFTModelSavingNativePaddingLoop.dispatch_fold_work h W q rest
      UniformFixedNetworkScheduleMachine.actualRoles (W-UniformFixedNetworkScheduleMachine.actualRoles)
      (DFTModelCacheRecords.dataTape (Instruction.record q .padding).data)
      ((q*m+rest,I),DFTModelRecursiveScalarSource.paired f f0)
      (headers.1.trans (UniformPaddingRecordProjections.opcode q))
      (headers.2.1.trans (UniformPaddingRecordProjections.columns q))
      (headers.2.2.1.trans (UniformPaddingRecordProjections.dest q))
      (headers.2.2.2.trans (UniformPaddingRecordProjections.source q))
    have widthBack:(m-1)+1=m:=by norm_num [m,ExplicitSeedBudget.m]
    simp only [widthBack] at tailWork
    have exactWork : (DFTModelSavingNativePaddingFold.steps h q rest
      UniformFixedNetworkScheduleMachine.actualRoles (W-UniformFixedNetworkScheduleMachine.actualRoles)
      ((q*m+rest,I),DFTModelRecursiveScalarSource.paired f f0)).work+
      (W-UniformFixedNetworkScheduleMachine.actualRoles)*(DFTModelSavingCost.unitAllowance+37)≤K*last := by
      exact tailWork
    have paid:109≤K*52:=by nlinarith only [fixed]
    have split:K*(52+last)=K*52+K*last:=by ring
    rw [split]
    exact (wh.trans (Nat.add_le_add_right exactWork 109)).trans
      (Nat.add_le_add_left paid (K*last) |>.trans_eq (Nat.add_comm _ _))

end
end ExactFourierCircuits.DFTModelSavingNativePaddingStep

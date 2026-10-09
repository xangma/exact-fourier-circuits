import UniformRecursiveTypedBody
import UniformRecursivePaddingSemantic
import UniformPaddingRecordProjections
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursivePaddingRecord
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine
open UniformNativeScheduleSemantics UniformRecursiveTypedBody
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursiveResidualEdge (Parent)
open UniformNativeHandlerSemantics (arrayValues)
namespace P
export UniformRecursiveSavingProgram (program address unitRecord unitLength)
end P
noncomputable section

lemma vector_padding (pc a b c d e f g:ℕ)(h:pc=(![a,b,c,d,e,f,g]) 5):pc=f:=h
lemma padding_pc (pc:ℕ)(h:pc=UniformRecursiveRecordControl.targets 5):pc=P.address .paddingInit:=
 vector_padding pc (P.address .residualMark) (P.address .scalar) (P.address .marker)
  (P.address .yRestore) (P.address .exchange) (P.address .paddingInit) (P.address .marker) h

lemma actual_good (q:ℕ):UniformFixedNetworkOpcodeMachine.WellFormed (Instruction.record q .padding):=by
 constructor
 · change 5 < 7;decide
 · rfl

lemma padding_parent {k q A F T rest stack depth:ℕ}{s t:State}
 (p:Parent k q A F T rest stack depth s)(cf:UniformRecursiveRecordControl.ControlFrame s t):
 UniformRecursivePaddingFrames.Parent k q A F rest stack depth t:=by
 have keep(j:ℕ)(hj:¬UniformRecursiveRecordControl.ControlChanged j):t.natReg j=s.natReg j:=cf.natReg j hj
 refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 all_goals first
 | exact (keep _ (by unfold UniformRecursiveRecordControl.ControlChanged;omega)).trans p.nativeBase
 | exact (keep _ (by unfold UniformRecursiveRecordControl.ControlChanged;omega)).trans p.original
 | exact (keep _ (by unfold UniformRecursiveRecordControl.ControlChanged;omega)).trans p.bits
 | exact (keep _ (by unfold UniformRecursiveRecordControl.ControlChanged;omega)).trans p.volume
 | exact (keep _ (by unfold UniformRecursiveRecordControl.ControlChanged;omega)).trans p.frontier
 | exact (keep _ (by unfold UniformRecursiveRecordControl.ControlChanged;omega)).trans p.rest
 | exact (keep _ (by unfold UniformRecursiveRecordControl.ControlChanged;omega)).trans p.stack
 | exact (keep _ (by unfold UniformRecursiveRecordControl.ControlChanged;omega)).trans p.depth
 | exact (keep _ (by unfold UniformRecursiveRecordControl.ControlChanged;omega)).trans p.one
 | exact (keep _ (by unfold UniformRecursiveRecordControl.ControlChanged;omega)).trans p.nativeBits
 | exact (keep _ (by unfold UniformRecursiveRecordControl.ControlChanged;omega)).trans p.nativeRest
 | exact (keep _ (by unfold UniformRecursiveRecordControl.ControlChanged;omega)).trans p.table
 | exact (keep _ (by unfold UniformRecursiveRecordControl.ControlChanged;omega)).trans p.columns
 | exact (keep _ (by unfold UniformRecursiveRecordControl.ControlChanged;omega)).trans p.width

/-- Raw opcode5 is physically decoded, then all actual padding roles run all
m same-q unit children before returning to the real parent record loop. -/
theorem execution (n B T tapeEnd U A F q rest stack depth stackTop reserve:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(s:State)(f:Fin W→Fin (2^(q*m+rest))→Scalar)
 (childIH:UniformRecursiveGroupExecution.SmallerBodies (q*m+rest) n B reserve stack stackTop cost x)
 (geometry:Geometry B A F q rest stack depth stackTop reserve)
 (pc:s.pc=P.address .loop)(parent:Parent (q*m+rest) q A F T rest stack depth s)
 (metadata:s.natHeap (F-1)=some tapeEnd)(live:T < tapeEnd)
 (printed:Printed T (Instruction.record q .padding).data s)
 (unitPointer:s.natHeap (F-2)=some U)(unitPrinted:Printed U (P.unitRecord.withColumns q).data s)
 (data:Present A W (2^(q*m+rest)) f s)
 (recordEnd:T+(Instruction.record q .padding).data.length ≤ B)
 (unitEnd:U+P.unitLength ≤ F-6)(unitAbove:stackTop ≤ U)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s):
 ∃u time,∃g:Fin W→Fin (2^(q*m+rest))→Scalar,
 BoundedRuns P.program n x B s time u ∧ u.pc=P.address .loop ∧
 Parent (q*m+rest) q A F (T+(Instruction.record q .padding).data.length) rest stack depth u ∧
 Present A W (2^(q*m+rest)) g u ∧
 arrayValues q rest g=(semantic q rest .padding).mulVec (arrayValues q rest f) ∧
 u.natHeap (F-1)=s.natHeap (F-1) ∧ u.natHeap (F-2)=s.natHeap (F-2) ∧
 (∀z,z < F→(z < stack+34*depth∨stackTop ≤ z)→z≠U+1→z≠U+3→
  z≠F-6→z≠F-5→z≠F-4→z≠F-3→u.natHeap z=s.natHeap z) ∧
 (∀z,z < F→(z < A∨A+W*2^(q*m+rest) ≤ z)→u.scalarHeap z=s.scalarHeap z) ∧
 UniformBinaryCStageMachine.Constants u ∧ u.rootOrders=s.rootOrders ∧ u.outputs=s.outputs ∧
 time ≤ 73+(W-actualRoles)*(64+m*UniformRecursiveResidualDirectionLoop.directionCost q (m-1) rest 32 cost):=by
 obtain ⟨t,control,tp,fields,body,saved,cf⟩:=UniformRecursiveRecordControl.read_dispatch_execution F T tapeEnd B n
  (Instruction.record q .padding) x s pc parent.frontier parent.cursor parent.one metadata live printed
  (actual_good q) bound recordEnd geometry.width geometry.code
 have fi:(⟨(Instruction.record q .padding).opcode,(actual_good q).1⟩:Fin 7)=5:=Fin.ext (by rfl)
 have entered:t.pc=P.address .paddingInit:=padding_pc t.pc (tp.trans (congrArg UniformRecursiveRecordControl.targets fi))
 have pp:=padding_parent parent cf
 have pointer:t.natHeap (F-2)=some U:=by rw [cf.natHeap];exact unitPointer
 have bank:Printed U (P.unitRecord.withColumns q).data t:=by intro j hj;rw [cf.natHeap];exact unitPrinted j hj
 have dataT:Present A W (2^(q*m+rest)) f t:=by intro i z;rw [cf.scalarHeap];exact data i z
 have ct:UniformBinaryCStageMachine.Constants t:=by unfold UniformBinaryCStageMachine.Constants at constants ⊢;rw [cf.scalarHeap];exact constants
 have dest:t.natReg 2854=actualRoles:=fields.dest.trans (UniformPaddingRecordProjections.dest q)
 have count:t.natReg 2855=W-actualRoles:=fields.source.trans (UniformPaddingRecordProjections.source q)
 have startBound:actualRoles ≤ W:=MasterBudget.seed_actual_padding
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
 obtain ⟨u,last,g,prior,run,up,cursor,pu,printU,gp,gv,m1,m2,nh,sh,cu,roots,outputs,lastBound⟩:=
  UniformRecursivePaddingExecution.execution n B U W A F q (m-1) rest stack depth stackTop reserve
   (T+(Instruction.record q .padding).data.length) actualRoles cost x t f childIH geometry.smaller entered pp saved dest count pointer
   (UniformRecursivePaddingExecution.printed_actual_in (m-1) q U widthEq t bank) dataT startBound
   geometry.positive m2 geometry.remainder geometry.batchFit unitSize geometry.width geometry.arrayEnd geometry.poolEnd
   geometry.square geometry.low geometry.base geometry.stackRoom unitAbove geometry.childRoom rolesBound ct control.final_bound geometry.code
 change UniformRecursivePaddingFrames.Parent (q*m+rest) q A F rest stack depth u at pu
 change Present A W (2^(q*m+rest)) g u at gp
 have fullParent:Parent (q*m+rest) q A F (T+(Instruction.record q .padding).data.length) rest stack depth u:=
  ⟨cursor,pu.nativeBase,pu.original,pu.bits,pu.volume,pu.frontier,pu.rest,pu.stack,pu.depth,pu.one,
   pu.nativeBits,pu.nativeRest,pu.table,pu.columns,pu.width⟩
 have values:arrayValues q rest g=(semantic q rest .padding).mulVec (arrayValues q rest f):=by
  apply UniformRecursivePaddingSemantic.padding_values q rest
  intro i
  funext z
  have h:=congrFun (congrFun gv i) z
  have act:=UniformRecursivePaddingExecution.action_remaining q (m-1) rest W actualRoles startBound
   (UniformRecursivePaddingArrays.values f) i
  rw [act] at h
  exact h
 refine ⟨u,52+last,g,?_,up,fullParent,gp,values,?_,?_,?_,?_,cu,
  roots.trans cf.roots,outputs.trans cf.outputs,?_⟩
 · convert control.trans run using 1
   simp only [UniformFixedNetworkOpcodeMachine.headCost,
    UniformRecursiveRecordControl.dispatchCost,UniformPaddingRecordProjections.opcode]
   norm_num
 · exact m1.trans (congrFun cf.natHeap (F-1))
 · exact m2.trans (congrFun cf.natHeap (F-2))
 · intro z hz away a b c d e f
   exact (nh z hz away a b c d e f).trans (congrFun cf.natHeap z)
 · intro z hz away;exact (sh z hz away).trans (congrFun cf.scalarHeap z)
 · unfold UniformRecursivePaddingRole.roleCost at lastBound
   change last ≤ (W-actualRoles)*(m*UniformRecursiveResidualDirectionLoop.directionCost q (m-1) rest 32 cost+58+6)+21 at lastBound
   have eq:m*UniformRecursiveResidualDirectionLoop.directionCost q (m-1) rest 32 cost+58+6=
    64+m*UniformRecursiveResidualDirectionLoop.directionCost q (m-1) rest 32 cost:=by omega
   rw [eq] at lastBound
   omega
end
end ExactFourierCircuits.UniformRecursivePaddingRecord

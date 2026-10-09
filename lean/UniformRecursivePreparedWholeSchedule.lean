import UniformRecursiveWholeSchedule
import UniformRecursivePreparedCoreSchedule
import UniformRecursivePreparedPaddingRecord
import UniformRecursivePaddingRecord
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveWholeSchedule
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine UniformNativeScheduleSemantics
open UniformRecursiveTypedBody UniformRecursiveCoreSchedule
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursiveResidualEdge (Parent)
open UniformNativeHandlerSemantics (arrayValues)
namespace P
export UniformRecursiveSavingProgram (program address seedLength unitLength unitRecord)
end P
noncomputable section
theorem execution_prepared (n B T U A F H q rest stack depth stackTop reserve:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(s:State)(f:Fin W→Fin (2^(q*m+rest))→Scalar)
 (childIH:UniformRecursiveGroupExecution.PreparedSmallerBodies (q*m+rest) n B reserve stack stackTop cost x)
 (geometry:Geometry B A F q rest stack depth stackTop reserve)
 (pc:s.pc=P.address .loop)(parent:Parent (q*m+rest) q A F T rest stack depth s)
 (metadata:s.natHeap (F-1)=some (T+P.seedLength))
 (printed:PrintedRecords T (scheduleRecords q) s)(data:Present A W (2^(q*m+rest)) f s)
 (unitPointer:s.natHeap (F-2)=some U)(unitPrinted:Printed U (P.unitRecord.withColumns q).data s)
 (mainEnd:T+P.seedLength ≤ F-6)(unitEnd:U+P.unitLength ≤ F-6)
 (stackEnd:stackTop ≤ T)(unitAbove:stackTop ≤ U)(floorUnit:H ≤ U)(floorWork:H ≤ F-6)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s):
 ∃u time,∃g:Fin W→Fin (2^(q*m+rest))→Scalar,
 BoundedRuns P.program n x B s time u ∧ u.pc=P.address .loop ∧
 Parent (q*m+rest) q A F (T+P.seedLength) rest stack depth u ∧
 Present A W (2^(q*m+rest)) g u ∧
 arrayValues q rest g=interpret q rest instructions (arrayValues q rest f) ∧
 u.natHeap (F-1)=s.natHeap (F-1) ∧ u.natHeap (F-2)=s.natHeap (F-2) ∧
 (∀z,z < H→(z < stack+34*depth∨stackTop ≤ z)→u.natHeap z=s.natHeap z) ∧
 (∀z,z < F→(z < A∨A+W*2^(q*m+rest) ≤ z)→u.scalarHeap z=s.scalarHeap z) ∧
 UniformBinaryCStageMachine.Constants u ∧ u.rootOrders=s.rootOrders ∧u.outputs=s.outputs ∧
 time ≤ (coreInstructions.map (ticks q rest cost)).sum+
  (73+(W-actualRoles)*(64+m*UniformRecursiveResidualDirectionLoop.directionCost q (m-1) rest 32 cost)) ∧ (UniformRecursivePreparedValues.Prepared2 f→UniformRecursivePreparedValues.Prepared2 g):=by
 obtain ⟨t,first,g,core,tp,pa,gp,gv,fr,ct,pad,firstBound,preparedG⟩:=UniformRecursiveCoreSchedule.execution_prepared n B T A F q rest
  stack depth stackTop reserve cost x s f childIH geometry pc parent metadata printed data mainEnd stackEnd constants bound
 have len:=core_length q
 have storedMeta:t.natHeap (F-1)=some (T+P.seedLength):=(fr.metadata geometry.low stackEnd (by omega)).trans metadata
 have ptr:t.natHeap (F-2)=some U:=by
  rw [fr.natHeap _ (by have h:=geometry.low;omega) (Or.inr (by omega)) (by have h:=geometry.low;omega)]
  exact unitPointer
 have bank:Printed U (P.unitRecord.withColumns q).data t:=by
  intro j hj
  have unchanged:(P.unitRecord.withColumns q).data.length=P.unitRecord.data.length:=by
   simp only [Record.data_length,Record.withColumns]
  have hlen:(P.unitRecord.withColumns q).data.length=P.unitLength:=
   unchanged.trans UniformRecursiveSavingProgram.unitRecord_length
  rw [hlen] at hj
  rw [fr.natHeap _ (by omega) (Or.inr (by omega)) (by omega)]
  exact unitPrinted j (by rwa [hlen])
 have fb:F ≤ B:=by have h:=geometry.poolEnd;omega
 obtain ⟨u,last,h,run,up,ph,hp,hv,m1,m2,nh,sh,cu,roots,outputs,lastBound,preparedH⟩:=UniformRecursivePaddingRecord.execution_prepared
  n B (T+(serialize (coreInstructions.map (Instruction.record q))).length) (T+P.seedLength) U A F q rest
  stack depth stackTop reserve cost x t g childIH geometry tp pa storedMeta (by omega) pad ptr bank gp
  (by rw [padding_length];omega) unitEnd unitAbove ct core.final_bound
 refine ⟨u,first+last,h,core.trans run,up,?_,hp,?_,?_,?_,?_,?_,cu,
  roots.trans fr.roots,outputs.trans fr.outputs,Nat.add_le_add firstBound lastBound,fun prep=>preparedH (preparedG prep)⟩
 · simpa only [padding_length,Nat.add_assoc,len] using ph
 · rw [instructions_core,interpret_append]
   change arrayValues q rest h=(semantic q rest .padding).mulVec (interpret q rest coreInstructions (arrayValues q rest f))
   rw [←gv];exact hv
 · exact m1.trans (fr.metadata geometry.low stackEnd (by omega))
 · exact m2.trans (fr.natHeap _ (by have h:=geometry.low;omega) (Or.inr (by omega)) (by have h:=geometry.low;omega))
 · intro z hz away
   exact (nh z (by omega) away (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
    (fr.natHeap z (by omega) away (by omega))
 · intro z hz away;exact (sh z hz away).trans (fr.scalarHeap z hz away)
end
end ExactFourierCircuits.UniformRecursiveWholeSchedule

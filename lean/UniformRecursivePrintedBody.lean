import UniformRecursiveWholeSchedule
import UniformRecursiveWholeValues
import UniformRecursiveSpectatorFinish
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursivePrintedBody
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine UniformNativeScheduleSemantics
open UniformRecursiveTypedBody UniformRecursiveCoreSchedule
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursiveResidualEdge (Parent)
open UniformNativeHandlerSemantics (arrayValues)
namespace P
export UniformRecursiveSavingProgram (program address seedLength unitLength unitRecord)
end P
noncomputable section

def bodyTicks (q rest:ℕ)(cost:ℕ→ℕ):ℕ:=
 (coreInstructions.map (ticks q rest cost)).sum+
 (73+(W-actualRoles)*(64+m*UniformRecursiveResidualDirectionLoop.directionCost q (m-1) rest 32 cost))+
 (4*(q*m)+W*UniformBinarySpectatorCMachine.arrayCost (q*m+rest) (q*m)+20)

/-- Whole physically printed large-node body, including the actual expired
record comparison and spectator suffix. No supplied matrix action enters. -/
theorem execution (n B T U A F H q rest stack depth stackTop reserve:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(s:State)(f:Fin W→Fin (2^(q*m+rest))→Scalar)
 (childIH:UniformRecursiveGroupExecution.SmallerBodies (q*m+rest) n B reserve stack stackTop cost x)
 (geometry:Geometry B A F q rest stack depth stackTop reserve)
 (pc:s.pc=P.address .loop)(parent:Parent (q*m+rest) q A F T rest stack depth s)
 (metadata:s.natHeap (F-1)=some (T+P.seedLength))
 (printed:PrintedRecords T (scheduleRecords q) s)(data:Present A W (2^(q*m+rest)) f s)
 (unitPointer:s.natHeap (F-2)=some U)(unitPrinted:Printed U (P.unitRecord.withColumns q).data s)
 (mainEnd:T+P.seedLength ≤ F-6)(unitEnd:U+P.unitLength ≤ F-6)
 (stackEnd:stackTop ≤ T)(unitAbove:stackTop ≤ U)(floorUnit:H ≤ U)(floorWork:H ≤ F-6)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s):
 ∃u time,∃g:Fin W→Fin (2^(q*m+rest))→Scalar,
 BoundedRuns P.program n x B s time u ∧u.pc=(if depth=0 then P.address .halt else P.address .returnSite)∧
 Present A W (2^(q*m+rest)) g u∧
 (∀i,(fun z=> (g i z).value)=(UniformBinaryTensorCoordinates.physicalMatrix (q*m+rest)).mulVec (fun z=> (f i z).value))∧
 u.natReg 4150=stack ∧u.natReg 4151=depth∧
 (∀z,z < H→(z < stack+34*depth∨stackTop ≤ z)→u.natHeap z=s.natHeap z)∧
 (∀z,z < F→(z < A∨A+W*2^(q*m+rest) ≤ z)→u.scalarHeap z=s.scalarHeap z)∧
 UniformBinaryCStageMachine.Constants u∧u.rootOrders=s.rootOrders∧u.outputs=s.outputs∧time ≤ bodyTicks q rest cost:=by
 obtain ⟨t,first,g,run,tp,pa,gp,gv,m1,m2,nh,sh,ct,roots,outputs,firstBound⟩:=UniformRecursiveWholeSchedule.execution
  n B T U A F H q rest stack depth stackTop reserve cost x s f childIH geometry pc parent metadata printed data
  unitPointer unitPrinted mainEnd unitEnd stackEnd unitAbove floorUnit floorWork constants bound
 have storedMeta:t.natHeap (F-1)=some (T+P.seedLength):=m1.trans metadata
 have width:t.natReg 4061=m:=by
  have eq:(q*m+rest-rest)/q=m:=by rw [Nat.add_sub_cancel_right];exact Nat.mul_div_right m (by have p:=geometry.positive;omega)
  exact pa.width.trans eq
 have countBound:W ≤ B:=by
  have pos:=Nat.two_pow_pos (q*m+rest)
  have a:=geometry.arrayEnd
  have b:=geometry.poolEnd
  nlinarith
 have extent:A+W*2^(q*m+rest) ≤ B:=geometry.arrayEnd.trans (by have h:=geometry.poolEnd;omega)
 have stride:2^(q*m)*2 ≤ B:=UniformBinarySpectatorCMachine.stride_bound
  (by omega) (by norm_num [W,ExplicitSeedBudget.paddedRoles,ExplicitSeedBudget.roleBits]) extent
 obtain ⟨u,v,last,up,out,lf,sf,cu⟩:=UniformRecursiveSpectatorFinish.terminal_execution
  n B (q*m+rest) q m A depth F (T+P.seedLength) (T+P.seedLength) x t g tp pa.cursor pa.frontier
  storedMeta (by omega) pa.one pa.bits pa.original pa.volume pa.columns width pa.depth gp (by omega) geometry.base ct
  run.final_bound geometry.code countBound extent stride
 let h:Fin W→Fin (2^(q*m+rest))→Scalar:=fun i=> UniformBinarySpectatorCMachine.transformed (q*m+rest) (q*m) (g i)
 have outH:Present A W (2^(q*m+rest)) h u:=out
 have values:∀i,(fun z=> (h i z).value)=(UniformBinaryTensorCoordinates.physicalMatrix (q*m+rest)).mulVec (fun z=> (f i z).value):=
  UniformRecursiveWholeValues.suffix_values q rest f g gv
 have keep(j:ℕ)(hj:¬UniformRecursiveSpectatorFinish.Changed j)(a:j≠3301)(b:j≠4178)(c:j≠4179):
  u.natReg j=t.natReg j:=(sf.natReg j hj).trans (lf.natReg j a b c)
 refine ⟨u,first+(4*(q*m)+W*UniformBinarySpectatorCMachine.arrayCost (q*m+rest) (q*m)+20),h,
  run.trans last,up,outH,values,?_,?_,?_,?_,cu,?_,?_,Nat.add_le_add_right firstBound _⟩
 · exact (keep _ (by unfold UniformRecursiveSpectatorFinish.Changed UniformRecursiveSpectatorFinish.SetupChanged UniformBinarySpectatorCMachine.Changed UniformBinaryTensorCMachine.Changed;omega) (by omega) (by omega) (by omega)).trans pa.stack
 · exact (keep _ (by unfold UniformRecursiveSpectatorFinish.Changed UniformRecursiveSpectatorFinish.SetupChanged UniformBinarySpectatorCMachine.Changed UniformBinaryTensorCMachine.Changed;omega) (by omega) (by omega) (by omega)).trans pa.depth
 · intro z hz away;exact (congrFun sf.natHeap z).trans ((congrFun lf.natHeap z).trans (nh z hz away))
 · intro z hz away;exact (sf.scalarHeap z away).trans ((congrFun lf.scalarHeap z).trans (sh z hz away))
 · exact sf.roots.trans (lf.roots.trans roots)
 · exact sf.outputs.trans (lf.outputs.trans outputs)
end
end ExactFourierCircuits.UniformRecursivePrintedBody

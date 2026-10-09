import UniformRecursivePreparedTypedBody
import UniformRecursiveCoreSchedule
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveCoreSchedule
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine
open UniformNativeScheduleSemantics UniformRecursiveTypedBody
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursiveResidualEdge (Parent)
open UniformNativeHandlerSemantics (arrayValues)
namespace P
export UniformRecursiveSavingProgram (program address seedLength)
end P
noncomputable section

theorem execution_prepared (n B T A F q rest stack depth stackTop reserve:ℕ)(cost:ℕ→ℕ)(x:Fin n→ℂ)
 (s:State)(f:Fin W→Fin (2^(q*m+rest))→Scalar)
 (childIH:UniformRecursiveGroupExecution.PreparedSmallerBodies (q*m+rest) n B reserve stack stackTop cost x)
 (geometry:Geometry B A F q rest stack depth stackTop reserve)
 (pc:s.pc=P.address .loop)(parent:Parent (q*m+rest) q A F T rest stack depth s)
 (metadata:s.natHeap (F-1)=some (T+P.seedLength))
 (printed:PrintedRecords T (scheduleRecords q) s)(data:Present A W (2^(q*m+rest)) f s)
 (mainEnd:T+P.seedLength ≤ F-6)(stackEnd:stackTop ≤ T)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s):
 ∃u time,∃g:Fin W→Fin (2^(q*m+rest))→Scalar,
 BoundedRuns P.program n x B s time u ∧ u.pc=P.address .loop ∧
 Parent (q*m+rest) q A F (T+(serialize (coreInstructions.map (Instruction.record q))).length) rest stack depth u ∧
 Present A W (2^(q*m+rest)) g u ∧
 arrayValues q rest g=interpret q rest coreInstructions (arrayValues q rest f) ∧
 Frame A F q rest stack depth stackTop s u ∧ UniformBinaryCStageMachine.Constants u ∧
 Printed (T+(serialize (coreInstructions.map (Instruction.record q))).length)
  (Instruction.record q .padding).data u ∧
 time ≤ (coreInstructions.map (ticks q rest cost)).sum ∧
 (UniformRecursivePreparedValues.Prepared2 f→UniformRecursivePreparedValues.Prepared2 g):=by
 have ph:PrintedRecords T ((coreInstructions.map (Instruction.record q))++[Instruction.record q .padding]) s:=by
  have eq:coreInstructions.map (Instruction.record q)++[Instruction.record q .padding]=scheduleRecords q:=by
   rw [←records_actual,instructions_core,List.map_append,List.map_cons,List.map_nil]
  rw [eq];exact printed
 obtain ⟨core,pad⟩:=printedRecords_append T _ _ s ph
 have lengthEq:=core_length q
 obtain ⟨u,time,g,run,up,parentOut,gp,gv,fr,cu,timeBound,prepared⟩:=run_records_prepared n B (T+P.seedLength) A F q rest
  stack depth stackTop reserve cost x coreInstructions childIH geometry core_noPadding mainEnd T s f pc parent
  metadata core data (by omega) stackEnd constants bound
 have outPad:Printed (T+(serialize (coreInstructions.map (Instruction.record q))).length)
  (Instruction.record q .padding).data u:=by
  intro j hj
  have boundj:T+(serialize (coreInstructions.map (Instruction.record q))).length+j < F-6:=by
   rw [padding_length] at hj;omega
  rw [fr.natHeap _ (by omega) (Or.inr (by omega)) (by omega)]
  exact pad.1 j hj
 exact ⟨u,time,g,run,up,parentOut,gp,gv,fr,cu,outPad,timeBound,prepared⟩
end
end ExactFourierCircuits.UniformRecursiveCoreSchedule

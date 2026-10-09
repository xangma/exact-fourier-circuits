import UniformRecursivePreparedNativeRecords
import UniformRecursiveTypedBody
import UniformRecursivePreparedResidualRecord
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveTypedBody
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine
open UniformNativeScheduleSemantics
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursiveResidualEdge (Parent)
open UniformNativeHandlerSemantics (arrayValues)
namespace P
export UniformRecursiveSavingProgram (program address)
end P
noncomputable section

theorem record_execution_prepared (n B T tapeEnd A F q rest stack depth stackTop reserve:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(i:TypedInstruction)(ni:NoPadding i)
 (s:State)(f:Fin W→Fin (2^(q*m+rest))→Scalar)
 (childIH:UniformRecursiveGroupExecution.PreparedSmallerBodies (q*m+rest) n B reserve stack stackTop cost x)
 (pc:s.pc=P.address .loop)(parent:Parent (q*m+rest) q A F T rest stack depth s)
 (metadata:s.natHeap (F-1)=some tapeEnd)(live:T < tapeEnd)
 (printed:Printed T (Instruction.record q i).data s)(data:Present A W (2^(q*m+rest)) f s)
 (geometry:Geometry B A F q rest stack depth stackTop reserve)
 (recordEnd:T+(Instruction.record q i).data.length ≤ F-6)(stackEnd:stackTop ≤ T)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s):
 ∃u time,∃g:Fin W→Fin (2^(q*m+rest))→Scalar,
 BoundedRuns P.program n x B s time u ∧ u.pc=P.address .loop ∧
 Parent (q*m+rest) q A F (T+(Instruction.record q i).data.length) rest stack depth u ∧
 Present A W (2^(q*m+rest)) g u ∧
 arrayValues q rest g=(semantic q rest i).mulVec (arrayValues q rest f) ∧
 Frame A F q rest stack depth stackTop s u ∧ UniformBinaryCStageMachine.Constants u ∧
 time ≤ ticks q rest cost i ∧
 (UniformRecursivePreparedValues.Prepared2 f→UniformRecursivePreparedValues.Prepared2 g):=by
 have fb:F ≤ B:=by have h:=geometry.poolEnd;omega
 cases i with
 | initial=>
  obtain ⟨u,g,run,up,h,out,val,fr,cu,prepared⟩:=UniformRecursiveNativeTypedRecords.marker_prepared n B T tapeEnd A F q rest stack depth x
   .initial (Or.inl rfl) s f pc parent metadata live printed data (by omega) geometry.width geometry.arrayEnd
   geometry.base constants bound geometry.code
  exact ⟨u,_,g,run,up,h,out,val,Frame.native fr,cu,le_rfl,prepared⟩
 | boundary a=>
  obtain ⟨u,g,run,up,h,out,val,fr,cu,prepared⟩:=UniformRecursiveNativeTypedRecords.marker_prepared n B T tapeEnd A F q rest stack depth x
   (.boundary a) (Or.inr ⟨a,rfl⟩) s f pc parent metadata live printed data (by omega) geometry.width geometry.arrayEnd
   geometry.base constants bound geometry.code
  exact ⟨u,_,g,run,up,h,out,val,Frame.native fr,cu,le_rfl,prepared⟩
 | «macro» a v=>
  cases v with
  | edge old new role edge=>
   obtain ⟨u,time,g,run,up,h,out,val,nh,sh,cu,roots,outputs,timeBound,prepared⟩:=UniformRecursiveResidualRecord.execution_prepared
    n B T tapeEnd A F q rest stack depth stackTop reserve cost x a role edge s f childIH geometry.smaller pc parent
    metadata live printed data geometry.positive geometry.remainder geometry.batchFit recordEnd geometry.width
    geometry.arrayEnd geometry.poolEnd geometry.square geometry.low geometry.base geometry.stackRoom stackEnd
    geometry.childRoom constants bound geometry.code
   exact ⟨u,time,g,run,up,h,out,val,⟨nh,sh,roots,outputs⟩,cu,timeBound,prepared⟩
  | shear d src ne c hc=>
   obtain ⟨u,g,run,up,h,out,val,fr,cu,prepared⟩:=UniformRecursiveNativeTypedRecords.scalar_prepared n B T tapeEnd A F q rest stack depth x a
    d src ne c hc s f pc parent metadata live printed data (by omega) geometry.width geometry.arrayEnd fb
    geometry.base constants bound geometry.code
   exact ⟨u,_,g,run,up,h,out,val,Frame.native fr,cu,le_rfl,prepared⟩
 | translation=>
  obtain ⟨u,g,run,up,h,out,val,fr,cu,prepared⟩:=UniformRecursiveNativeTypedRecords.translation_prepared n B T tapeEnd A F q rest stack depth x
   s f pc parent metadata live printed data (by omega) geometry.width geometry.arrayEnd geometry.poolEnd
   geometry.square geometry.base geometry.positive geometry.remainder constants bound geometry.code
  exact ⟨u,_,g,run,up,h,out,val,Frame.native fr,cu,le_rfl,prepared⟩
 | exchange=>
  obtain ⟨u,g,run,up,h,out,val,fr,cu,prepared⟩:=UniformRecursiveNativeTypedRecords.exchange_prepared n B T tapeEnd A F q rest stack depth x
   s f pc parent metadata live printed data (by omega) geometry.width geometry.arrayEnd fb geometry.base
   constants bound geometry.code
  exact ⟨u,_,g,run,up,h,out,val,Frame.native fr,cu,le_rfl,prepared⟩
 | padding=>exact False.elim ni

/-- Actual continuous finite-record execution. This theorem uses the closed
handler family above, and never assumes an opaque record action or callback. -/
theorem run_records_prepared (n B tapeEnd A F q rest stack depth stackTop reserve:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(is:List TypedInstruction)
 (childIH:UniformRecursiveGroupExecution.PreparedSmallerBodies (q*m+rest) n B reserve stack stackTop cost x)
 (geometry:Geometry B A F q rest stack depth stackTop reserve)
 (noPadding:∀i∈is,NoPadding i)(mainEnd:tapeEnd ≤ F-6):
 ∀(T:ℕ)(s:State)(f:Fin W→Fin (2^(q*m+rest))→Scalar),
 s.pc=P.address .loop→Parent (q*m+rest) q A F T rest stack depth s→
 s.natHeap (F-1)=some tapeEnd→PrintedRecords T (is.map (Instruction.record q)) s→
 Present A W (2^(q*m+rest)) f s→T+(serialize (is.map (Instruction.record q))).length ≤ tapeEnd→
 stackTop ≤ T→UniformBinaryCStageMachine.Constants s→WordBound B s→
 ∃u time,∃g:Fin W→Fin (2^(q*m+rest))→Scalar,
 BoundedRuns P.program n x B s time u ∧ u.pc=P.address .loop ∧
 Parent (q*m+rest) q A F (T+(serialize (is.map (Instruction.record q))).length) rest stack depth u ∧
 Present A W (2^(q*m+rest)) g u ∧
 arrayValues q rest g=interpret q rest is (arrayValues q rest f) ∧
 Frame A F q rest stack depth stackTop s u ∧ UniformBinaryCStageMachine.Constants u ∧
 time ≤ (is.map (ticks q rest cost)).sum ∧
 (UniformRecursivePreparedValues.Prepared2 f→UniformRecursivePreparedValues.Prepared2 g):=by
 induction is with
 | nil=>
  intro T s f pc parent metadata printed data endBound stackEnd constants bound
  refine ⟨s,0,f,.refl bound,pc,?_,data,?_,Frame.refl A F q rest stack depth stackTop s,constants,?_,fun h=>h⟩
  · simpa only [List.map_nil,serialize,List.flatten_nil,List.length_nil,Nat.add_zero] using parent
  · rfl
  · exact le_rfl
 | cons i is ih=>
  intro T s f pc parent metadata printed data endBound stackEnd constants bound
  have lengths:(serialize ((i::is).map (Instruction.record q))).length=
   (Instruction.record q i).data.length+(serialize (is.map (Instruction.record q))).length:=by
   exact serialized_cons _ _
  have split:Printed T (Instruction.record q i).data s ∧
   PrintedRecords (T+(Instruction.record q i).data.length) (is.map (Instruction.record q)) s:=printed
  have endSingle:T+(Instruction.record q i).data.length ≤ F-6:=by rw [lengths] at endBound;omega
  have live:T < tapeEnd:=by have pos:=record_positive (Instruction.record q i);rw [lengths] at endBound;omega
  obtain ⟨t,first,g,run,tp,ph,gp,gv,fr,ct,timeBound,preparedG⟩:=record_execution_prepared n B T tapeEnd A F q rest stack depth stackTop reserve
   cost x i (noPadding i (by simp)) s f childIH pc parent metadata live split.1 data geometry endSingle stackEnd constants bound
  have nextBank:PrintedRecords (T+(Instruction.record q i).data.length) (is.map (Instruction.record q)) t:=
   printedRecords_transport fr _ split.2 (by omega) (by rw [lengths] at endBound;omega)
  have nextMetadata:t.natHeap (F-1)=some tapeEnd:=
   (fr.metadata geometry.low stackEnd (by omega)).trans metadata
  obtain ⟨u,remaining,h,tail,up,uh,hp,hv,tf,cu,remainingBound,preparedH⟩:=ih
   (by intro j hj;exact noPadding j (by simp [hj]))
   (T+(Instruction.record q i).data.length) t g tp ph nextMetadata nextBank gp
   (by rw [lengths] at endBound;omega) (by omega) ct run.final_bound
  refine ⟨u,first+remaining,h,run.trans tail,up,?_,hp,?_,fr.trans tf,cu,?_,fun h=>preparedH (preparedG h)⟩
  · simpa only [lengths,Nat.add_assoc] using uh
  · change arrayValues q rest h=interpret q rest is ((semantic q rest i).mulVec (arrayValues q rest f))
    rw [←gv];exact hv
  · simp only [List.map_cons,List.sum_cons]
    exact Nat.add_le_add timeBound remainingBound

end
end ExactFourierCircuits.UniformRecursiveTypedBody

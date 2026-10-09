import UniformRecursiveTypedBody
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

def coreInstructions:List TypedInstruction:=
 .initial::(fixedInvocations.map (fun a=>.boundary a::(encodedBlock a).map (.macro a))).flatten++
 [.translation,.exchange]

lemma instructions_core:instructions=coreInstructions++[.padding]:=by
 simp only [instructions,coreInstructions,List.cons_append,List.append_assoc,List.nil_append]

lemma core_noPadding:∀i∈coreInstructions,NoPadding i:=by
 intro i hi
 rcases List.mem_cons.mp hi with rfl|hi
 · trivial
 rcases List.mem_append.mp hi with block|last
 · obtain ⟨b,hb,ib⟩:=List.mem_flatten.mp block
   obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hb
   rcases List.mem_cons.mp ib with rfl|ib
   · trivial
   obtain ⟨v,hv,rfl⟩:=List.mem_map.mp ib
   trivial
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at last
   rcases last with rfl|rfl <;> trivial

lemma padding_length (q:ℕ):(Instruction.record q .padding).data.length=8:=rfl
lemma full_length (q:ℕ):(serialize (instructions.map (Instruction.record q))).length=P.seedLength:=by
 rw [records_actual]
 exact schedule_size_independent q
lemma core_length (q:ℕ):
 (serialize (coreInstructions.map (Instruction.record q))).length+8=P.seedLength:=by
 have eq:=full_length q
 rw [instructions_core,List.map_append] at eq
 simpa only [serialize,List.map_append,List.flatten_append,List.length_append,
  List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,padding_length] using eq

lemma printedRecords_append (T:ℕ)(rs ts:List Record)(s:State)(h:PrintedRecords T (rs++ts) s):
 PrintedRecords T rs s ∧ PrintedRecords (T+(serialize rs).length) ts s:=by
 induction rs generalizing T with
 | nil=>exact ⟨trivial,by simpa only [serialize,List.map_nil,List.flatten_nil,List.length_nil,Nat.add_zero,List.nil_append] using h⟩
 | cons r rs ih=>
  obtain ⟨a,b⟩:=ih (T+r.data.length) h.2
  refine ⟨⟨h.1,a⟩,?_⟩
  simpa only [serialized_cons,Nat.add_assoc] using b

/-- Actual common Program executes the entire nonpadding fixed network from
its real printer output. No record-loop or matrix-action premise remains. -/
theorem execution (n B T A F q rest stack depth stackTop reserve:ℕ)(cost:ℕ→ℕ)(x:Fin n→ℂ)
 (s:State)(f:Fin W→Fin (2^(q*m+rest))→Scalar)
 (childIH:UniformRecursiveGroupExecution.SmallerBodies (q*m+rest) n B reserve stack stackTop cost x)
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
 time ≤ (coreInstructions.map (ticks q rest cost)).sum:=by
 have ph:PrintedRecords T ((coreInstructions.map (Instruction.record q))++[Instruction.record q .padding]) s:=by
  have eq:coreInstructions.map (Instruction.record q)++[Instruction.record q .padding]=scheduleRecords q:=by
   rw [←records_actual,instructions_core,List.map_append,List.map_cons,List.map_nil]
  rw [eq];exact printed
 obtain ⟨core,pad⟩:=printedRecords_append T _ _ s ph
 have lengthEq:=core_length q
 obtain ⟨u,time,g,run,up,parentOut,gp,gv,fr,cu,timeBound⟩:=run_records n B (T+P.seedLength) A F q rest
  stack depth stackTop reserve cost x coreInstructions childIH geometry core_noPadding mainEnd T s f pc parent
  metadata core data (by omega) stackEnd constants bound
 have outPad:Printed (T+(serialize (coreInstructions.map (Instruction.record q))).length)
  (Instruction.record q .padding).data u:=by
  intro j hj
  have boundj:T+(serialize (coreInstructions.map (Instruction.record q))).length+j < F-6:=by
   rw [padding_length] at hj;omega
  rw [fr.natHeap _ (by omega) (Or.inr (by omega)) (by omega)]
  exact pad.1 j hj
 exact ⟨u,time,g,run,up,parentOut,gp,gv,fr,cu,outPad,timeBound⟩
end
end ExactFourierCircuits.UniformRecursiveCoreSchedule

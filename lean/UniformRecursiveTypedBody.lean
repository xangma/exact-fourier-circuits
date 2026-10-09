import UniformRecursiveNativeTypedRecords
import UniformRecursiveResidualRecord
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

abbrev TypedInstruction:=UniformNativeScheduleSemantics.Instruction

def NoPadding:TypedInstruction→Prop
 | .padding=>False
 | _=>True

def ticks (q rest:ℕ)(cost:ℕ→ℕ):TypedInstruction→ℕ
 | .macro a (.edge old new role edge)=>edge.dimension*UniformRecursiveResidualDirectionLoop.directionCost q (m-1) rest
    (UniformFixedNetworkOpcodeMachine.headCost (Instruction.record q (.macro a (.edge old new role edge)))) cost+53
 | .macro _ (.shear _ _ _ c _)=>10*2^(q*m+rest)+4*(q*m+rest)+c.val+102
 | .translation=>UniformNativeYRecordMachine.runtime q m rest (q*m+rest) UniformNativeHandlerSemantics.actualDirections.length+51
 | .exchange=>(10*2^(q*m+rest)+21)*UniformNativeHandlerSemantics.actualPairs.length+4*(q*m+rest)+99
 | i=>6+2*UniformFixedNetworkOpcodeMachine.headCost (Instruction.record q i)+
    UniformRecursiveRecordControl.dispatchCost (Instruction.record q i).opcode

structure Geometry (B A F q rest stack depth stackTop reserve:ℕ):Prop where
 positive:1 ≤ q
 remainder:rest < m
 smaller:q < q*m+rest
 batchFit:ExplicitSeedBudget.roleBits ≤ q*(m-1)+rest
 width:m+1 ≤ B
 arrayEnd:A+W*2^(q*m+rest) ≤ F
 poolEnd:F+5*2^(q*m+rest) ≤ B
 square:(2^(q*m+rest))^2 ≤ B
 low:6 ≤ F
 base:3 ≤ A
 stackRoom:stack+34*(depth+q+2) ≤ stackTop
 childRoom:F+5*2^(q*m+rest)+reserve*(q+1)*2^q ≤ B
 code:P.program.length ≤ B

/-- Every low table cell outside the actual recursive stack is retained,
except the one charged edge/padding mode cell. -/
structure Frame (A F q rest stack depth stackTop:ℕ)(s u:State):Prop where
 natHeap:∀z,z < F→(z < stack+34*depth∨stackTop ≤ z)→z≠F-6→u.natHeap z=s.natHeap z
 scalarHeap:∀z,z < F→(z < A∨A+W*2^(q*m+rest) ≤ z)→u.scalarHeap z=s.scalarHeap z
 roots:u.rootOrders=s.rootOrders
 outputs:u.outputs=s.outputs

lemma Frame.refl (A F q rest stack depth stackTop:ℕ)(s:State):Frame A F q rest stack depth stackTop s s:=
 ⟨fun _ _ _ _=>rfl,fun _ _ _=>rfl,rfl,rfl⟩
lemma Frame.trans {A F q rest stack depth stackTop:ℕ}{s t u:State}
 (a:Frame A F q rest stack depth stackTop s t)(b:Frame A F q rest stack depth stackTop t u):
 Frame A F q rest stack depth stackTop s u:=
 ⟨fun z hz away ne=>(b.natHeap z hz away ne).trans (a.natHeap z hz away ne),
  fun z hz away=>(b.scalarHeap z hz away).trans (a.scalarHeap z hz away),b.roots.trans a.roots,b.outputs.trans a.outputs⟩
lemma Frame.native {A F q rest stack depth stackTop:ℕ}{s u:State}
 (h:UniformRecursiveNativeTypedRecords.Frame A (2^(q*m+rest)) F s u):Frame A F q rest stack depth stackTop s u:=
 ⟨fun z hz _ _=>h.natHeap z hz,h.scalarHeap,h.roots,h.outputs⟩

lemma Frame.metadata {A F q rest stack depth stackTop T:ℕ}{s u:State}
 (fr:Frame A F q rest stack depth stackTop s u)(low:6 ≤ F)(stackEnd:stackTop ≤ T)(endBound:T ≤ F-6):
 u.natHeap (F-1)=s.natHeap (F-1):=fr.natHeap _ (by omega) (Or.inr (by omega)) (by omega)

lemma serialized_cons (r:Record)(rs:List Record):
 (serialize (r::rs)).length=r.data.length+(serialize rs).length:=by
 simp only [serialize,List.map_cons,List.flatten_cons,List.length_append]
lemma record_positive (r:Record):0 < r.data.length:=by rw [Record.data_length];omega

lemma printedRecords_transport {A F q rest stack depth stackTop T:ℕ}{s u:State}
 (fr:Frame A F q rest stack depth stackTop s u)(rs:List Record)
 (printed:PrintedRecords T rs s)(stackEnd:stackTop ≤ T)(endBound:T+(serialize rs).length ≤ F-6):
 PrintedRecords T rs u:=by
 induction rs generalizing T with
 | nil=>trivial
 | cons r rs ih=>
  change Printed T r.data u ∧ PrintedRecords (T+r.data.length) rs u
  have bounds:T+r.data.length+(serialize rs).length ≤ F-6:=by
   rw [serialized_cons] at endBound;omega
  refine ⟨?_,ih printed.2 (by omega) bounds⟩
  intro j hj
  rw [fr.natHeap _ (by omega) (Or.inr (by omega)) (by omega)]
  exact printed.1 j hj

/-- Closed actual handler family for all nonpadding typed records. The only
recursive assumption is real execution of the identical Program at q<k. -/
theorem record_execution (n B T tapeEnd A F q rest stack depth stackTop reserve:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(i:TypedInstruction)(ni:NoPadding i)
 (s:State)(f:Fin W→Fin (2^(q*m+rest))→Scalar)
 (childIH:UniformRecursiveGroupExecution.SmallerBodies (q*m+rest) n B reserve stack stackTop cost x)
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
 time ≤ ticks q rest cost i:=by
 have fb:F ≤ B:=by have h:=geometry.poolEnd;omega
 cases i with
 | initial=>
  obtain ⟨u,g,run,up,h,out,val,fr,cu⟩:=UniformRecursiveNativeTypedRecords.marker n B T tapeEnd A F q rest stack depth x
   .initial (Or.inl rfl) s f pc parent metadata live printed data (by omega) geometry.width geometry.arrayEnd
   geometry.base constants bound geometry.code
  exact ⟨u,_,g,run,up,h,out,val,Frame.native fr,cu,le_rfl⟩
 | boundary a=>
  obtain ⟨u,g,run,up,h,out,val,fr,cu⟩:=UniformRecursiveNativeTypedRecords.marker n B T tapeEnd A F q rest stack depth x
   (.boundary a) (Or.inr ⟨a,rfl⟩) s f pc parent metadata live printed data (by omega) geometry.width geometry.arrayEnd
   geometry.base constants bound geometry.code
  exact ⟨u,_,g,run,up,h,out,val,Frame.native fr,cu,le_rfl⟩
 | «macro» a v=>
  cases v with
  | edge old new role edge=>
   obtain ⟨u,time,g,run,up,h,out,val,nh,sh,cu,roots,outputs,timeBound⟩:=UniformRecursiveResidualRecord.execution
    n B T tapeEnd A F q rest stack depth stackTop reserve cost x a role edge s f childIH geometry.smaller pc parent
    metadata live printed data geometry.positive geometry.remainder geometry.batchFit recordEnd geometry.width
    geometry.arrayEnd geometry.poolEnd geometry.square geometry.low geometry.base geometry.stackRoom stackEnd
    geometry.childRoom constants bound geometry.code
   exact ⟨u,time,g,run,up,h,out,val,⟨nh,sh,roots,outputs⟩,cu,timeBound⟩
  | shear d src ne c hc=>
   obtain ⟨u,g,run,up,h,out,val,fr,cu⟩:=UniformRecursiveNativeTypedRecords.scalar n B T tapeEnd A F q rest stack depth x a
    d src ne c hc s f pc parent metadata live printed data (by omega) geometry.width geometry.arrayEnd fb
    geometry.base constants bound geometry.code
   exact ⟨u,_,g,run,up,h,out,val,Frame.native fr,cu,le_rfl⟩
 | translation=>
  obtain ⟨u,g,run,up,h,out,val,fr,cu⟩:=UniformRecursiveNativeTypedRecords.translation n B T tapeEnd A F q rest stack depth x
   s f pc parent metadata live printed data (by omega) geometry.width geometry.arrayEnd geometry.poolEnd
   geometry.square geometry.base geometry.positive geometry.remainder constants bound geometry.code
  exact ⟨u,_,g,run,up,h,out,val,Frame.native fr,cu,le_rfl⟩
 | exchange=>
  obtain ⟨u,g,run,up,h,out,val,fr,cu⟩:=UniformRecursiveNativeTypedRecords.exchange n B T tapeEnd A F q rest stack depth x
   s f pc parent metadata live printed data (by omega) geometry.width geometry.arrayEnd fb geometry.base
   constants bound geometry.code
  exact ⟨u,_,g,run,up,h,out,val,Frame.native fr,cu,le_rfl⟩
 | padding=>exact False.elim ni

/-- Actual continuous finite-record execution. This theorem uses the closed
handler family above, and never assumes an opaque record action or callback. -/
theorem run_records (n B tapeEnd A F q rest stack depth stackTop reserve:ℕ)
 (cost:ℕ→ℕ)(x:Fin n→ℂ)(is:List TypedInstruction)
 (childIH:UniformRecursiveGroupExecution.SmallerBodies (q*m+rest) n B reserve stack stackTop cost x)
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
 time ≤ (is.map (ticks q rest cost)).sum:=by
 induction is with
 | nil=>
  intro T s f pc parent metadata printed data endBound stackEnd constants bound
  refine ⟨s,0,f,.refl bound,pc,?_,data,?_,Frame.refl A F q rest stack depth stackTop s,constants,?_⟩
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
  obtain ⟨t,first,g,run,tp,ph,gp,gv,fr,ct,timeBound⟩:=record_execution n B T tapeEnd A F q rest stack depth stackTop reserve
   cost x i (noPadding i (by simp)) s f childIH pc parent metadata live split.1 data geometry endSingle stackEnd constants bound
  have nextBank:PrintedRecords (T+(Instruction.record q i).data.length) (is.map (Instruction.record q)) t:=
   printedRecords_transport fr _ split.2 (by omega) (by rw [lengths] at endBound;omega)
  have nextMetadata:t.natHeap (F-1)=some tapeEnd:=
   (fr.metadata geometry.low stackEnd (by omega)).trans metadata
  obtain ⟨u,remaining,h,tail,up,uh,hp,hv,tf,cu,remainingBound⟩:=ih
   (by intro j hj;exact noPadding j (by simp [hj]))
   (T+(Instruction.record q i).data.length) t g tp ph nextMetadata nextBank gp
   (by rw [lengths] at endBound;omega) (by omega) ct run.final_bound
  refine ⟨u,first+remaining,h,run.trans tail,up,?_,hp,?_,fr.trans tf,cu,?_⟩
  · simpa only [lengths,Nat.add_assoc] using uh
  · change arrayValues q rest h=interpret q rest is ((semantic q rest i).mulVec (arrayValues q rest f))
    rw [←gv];exact hv
  · simp only [List.map_cons,List.sum_cons]
    exact Nat.add_le_add timeBound remainingBound

end
end ExactFourierCircuits.UniformRecursiveTypedBody

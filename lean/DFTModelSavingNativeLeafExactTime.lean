import DFTModelSavingNativeLeafTyped

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeLeafExactTime
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine
open UniformNativeScheduleSemantics UniformRecursiveTypedBody
open UniformFixedNetworkShearChildMachine (Present shearValues)
open UniformRecursiveResidualEdge (Parent)
open UniformNativeHandlerSemantics (arrayValues roleMap)
open DFTModelClockControl DFTModelAffine DFTModelAdmissibilityControl
open DFTModelRecursiveScalarSource (paired)
open DFTModelSavingNativeSequence
namespace P
export UniformRecursiveSavingProgram (program address)
end P
noncomputable section
attribute [local irreducible] P.program DFTModelSavingRecords.dispatch

abbrev Leaf := DFTModelSavingNativeLeafTyped.Leaf

lemma marker (n B T tapeEnd A F q rest stack depth stackTop reserve : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (I : ℂ) (h : Handler ChildPort)
    (i : TypedInstruction) (hi : i=.initial∨∃a,i=.boundary a)
    (s s0 : State) (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (same : StateMatch s s0) (pc : s.pc=P.address .loop)
    (parent : Parent (q*m+rest) q A F T rest stack depth s)
    (metadata : s.natHeap (F-1)=some tapeEnd) (live : T<tapeEnd)
    (printed : Printed T (Instruction.record q i).data s)
    (data : Present A W (2^(q*m+rest)) f s) (data0 : Present A W (2^(q*m+rest)) f0 s0)
    (geometry : Geometry B A F q rest stack depth stackTop reserve)
    (recordEnd : T+(Instruction.record q i).data.length≤F-6)
    (constants : UniformBinaryCStageMachine.Constants s) (bound : WordBound B s) :
    ∃u u0 g g0,StepResult n B T A F q rest stack depth stackTop cost x I h i s s0 f f0 u u0 (ticks q rest cost i) g g0 := by
  have good:=UniformRecursiveNativeTypedRecords.marker_good q i hi
  have width:(Instruction.record q i).width+1≤B:=by
    rcases hi with rfl|⟨a,rfl⟩ <;> exact geometry.width
  have fb:F≤B:=by have k:=geometry.poolEnd;omega
  obtain ⟨u,u0,run,run0,matched,up,up0,parentOut,parent0,out,out0,fr,fr0,compiled⟩:=
    DFTModelSavingNativeMarker.execution q (q*m+rest) A T F tapeEnd rest stack depth B n x
      (Instruction.record q i) s s0 f f0 I h same pc parent metadata live printed good.2 good.1
      data data0 bound geometry.code (by omega) width
  have tickEq : 6+2*UniformFixedNetworkOpcodeMachine.headCost (Instruction.record q i)+
      UniformRecursiveRecordControl.dispatchCost (Instruction.record q i).opcode=ticks q rest cost i := by
    rcases hi with rfl|⟨a,rfl⟩ <;> rfl
  rw [tickEq] at run run0
  refine ⟨u,u0,f,f0,run,run0,matched,up,up0,parentOut,parent0,out,out0,?_,?_,
    Frame.native fr,Frame.native fr0,fr.constants geometry.base geometry.arrayEnd constants,
    fr0.constants geometry.base geometry.arrayEnd (DFTModelSavingNativeExchange.constants_match same constants),?_,compiled⟩
  · rcases hi with rfl|⟨a,rfl⟩
    · exact (UniformNativeHandlerSemantics.initial_values q rest f).symm
    · exact (UniformNativeHandlerSemantics.boundary_values q rest a f).symm
  · rcases hi with rfl|⟨a,rfl⟩
    · exact (UniformNativeHandlerSemantics.initial_values q rest f0).symm
    · exact (UniformNativeHandlerSemantics.boundary_values q rest a f0).symm
  · rcases hi with rfl|⟨a,rfl⟩ <;> exact le_rfl

/-- All nonrecursive real instruction forms are paired source executions of
this fixed saving program. The concrete residual/padding joins supply the two
remaining forms in the complete record family. -/
theorem execution (n B T tapeEnd A F q rest stack depth stackTop reserve : ℕ)
    (cost : ℕ→ℕ) (x : Fin n→ℂ) (I : ℂ) (h : Handler ChildPort)
    (i : TypedInstruction) (leaf : Leaf i)
    (s s0 : State) (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (same : StateMatch s s0) (pc : s.pc=P.address .loop)
    (parent : Parent (q*m+rest) q A F T rest stack depth s)
    (metadata : s.natHeap (F-1)=some tapeEnd) (live : T<tapeEnd)
    (printed : Printed T (Instruction.record q i).data s)
    (data : Present A W (2^(q*m+rest)) f s) (data0 : Present A W (2^(q*m+rest)) f0 s0)
    (geometry : Geometry B A F q rest stack depth stackTop reserve)
    (recordEnd : T+(Instruction.record q i).data.length≤F-6)
    (constants : UniformBinaryCStageMachine.Constants s) (bound : WordBound B s) :
    ∃u u0 g g0,StepResult n B T A F q rest stack depth stackTop cost x I h i s s0 f f0 u u0 (ticks q rest cost i) g g0 := by
  have fb:F≤B:=by have k:=geometry.poolEnd;omega
  cases i with
  | initial=>
    exact marker n B T tapeEnd A F q rest stack depth stackTop reserve cost x I h .initial
      (Or.inl rfl) s s0 f f0 same pc parent metadata live printed data data0 geometry recordEnd constants bound
  | boundary a=>
    exact marker n B T tapeEnd A F q rest stack depth stackTop reserve cost x I h (.boundary a)
      (Or.inr ⟨a,rfl⟩) s s0 f f0 same pc parent metadata live printed data data0 geometry recordEnd constants bound
  | «macro» a v=>
    cases v with
    | edge old new role edge=>exact False.elim leaf
    | shear d src ne c hc=>
      let di:=roleMap ((fixedBlock a).embedding d)
      let si:=roleMap ((fixedBlock a).embedding src)
      have neq:di≠si:=fun he=>ne ((fixedBlock a).embedding.injective (roleMap.injective he))
      have recordEq:=UniformNativeHandlerSemantics.scalar_record q a d src ne c hc
      change UniformNativeScalarRecordMachine.shearRecord q m di si c=_ at recordEq
      have bank:Printed T (UniformNativeScalarRecordMachine.shearRecord q m di si c).data s:=by
        rw [recordEq];exact printed
      have len:(Instruction.record q (.macro a (.shear d src ne c hc))).data.length=8:=rfl
      have endBound:T+8≤B:=by rw [len] at recordEnd;omega
      obtain ⟨u,u0,run,run0,matched,up,up0,parentOut,parent0,out,out0,fr,fr0,heap,compiled⟩:=
        DFTModelSavingNativeScalar.execution q m (q*m+rest) A T F tapeEnd rest stack depth B n x
          di si neq c s s0 f f0 I h same pc parent metadata live bank data data0 bound geometry.code
          endBound geometry.width (geometry.arrayEnd.trans fb)
      let g:=shearValues di si (UniformFixedCoefficientCodec.decode c) f
      let g0:=shearValues di si (UniformFixedCoefficientCodec.decode c) f0
      have p:Parent (q*m+rest) q A F
          (T+(Instruction.record q (.macro a (.shear d src ne c hc))).data.length) rest stack depth u:=by
        rw [len];exact parentOut
      have p0:Parent (q*m+rest) q A F
          (T+(Instruction.record q (.macro a (.shear d src ne c hc))).data.length) rest stack depth u0:=by
        rw [len];exact parent0
      have compiled':DFTModelSavingChronology.recordStep W rest h
          (Instruction.record q (.macro a (.shear d src ne c hc))) ((q*m+rest,I),paired f f0)=
          ((q*m+rest,I),paired g g0):=by
        unfold DFTModelSavingChronology.recordStep
        rw [←recordEq]
        exact compiled
      exact ⟨u,u0,g,g0,run,run0,matched,up,up0,p,p0,out,out0,
        (UniformNativeHandlerSemantics.scalar_values q rest a d src ne c hc f).symm,
        (UniformNativeHandlerSemantics.scalar_values q rest a d src ne c hc f0).symm,
        Frame.native fr,Frame.native fr0,fr.constants geometry.base geometry.arrayEnd constants,
        fr0.constants geometry.base geometry.arrayEnd (DFTModelSavingNativeExchange.constants_match same constants),
        le_rfl,compiled'⟩
  | translation=>
    obtain ⟨u,u0,run,run0,matched,up,up0,p,p0,out,out0,fr,fr0,con,con0,compiled,valid⟩:=
      DFTModelSavingNativeY.actual_execution n B T tapeEnd A F q rest stack depth x s s0 I h f f0 same
        pc parent metadata live printed data data0 (by omega) geometry.width geometry.arrayEnd geometry.poolEnd
        geometry.square geometry.base geometry.positive geometry.remainder constants bound geometry.code
    exact ⟨u,u0,_,_,run,run0,matched,up,up0,p,p0,out,out0,
      (UniformNativeHandlerSemantics.translation_values q rest f).symm,
      (UniformNativeHandlerSemantics.translation_values q rest f0).symm,
      Frame.native fr,Frame.native fr0,con,con0,le_rfl,compiled⟩
  | exchange=>
    obtain ⟨u,u0,run,run0,matched,up,up0,p,p0,out,out0,fr,fr0,con,con0,compiled,valid⟩:=
      DFTModelSavingNativeExchange.actual_execution n B T tapeEnd A F q rest stack depth x s s0 I h f f0 same
        pc parent metadata live printed data data0 (by omega) geometry.width geometry.arrayEnd fb
        geometry.base constants bound geometry.code
    exact ⟨u,u0,_,_,run,run0,matched,up,up0,p,p0,out,out0,
      (UniformNativeHandlerSemantics.exchange_values q rest f).symm,
      (UniformNativeHandlerSemantics.exchange_values q rest f0).symm,
      Frame.native fr,Frame.native fr0,con,con0,le_rfl,compiled⟩
  | padding=>exact False.elim leaf

end
end ExactFourierCircuits.DFTModelSavingNativeLeafExactTime

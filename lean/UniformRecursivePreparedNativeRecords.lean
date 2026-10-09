import UniformRecursivePreparedValues
import UniformRecursiveNativeTypedRecords
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveNativeTypedRecords
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine
open UniformNativeScheduleSemantics
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursiveResidualEdge (Parent)
open UniformNativeHandlerSemantics (arrayValues roleMap)
noncomputable section
theorem scalar_prepared (n B T tapeEnd A F q rest stack depth:ℕ)(x:Fin n→ℂ)(a:Invocation)
 (d src:Fin (fixedBlock a).width)(ne:d≠src)(c:Fin 5)(hc:UniformFixedCoefficientCodec.decode c≠0)
 (s:State)(f:Fin W→Fin (2^(q*m+rest))→Scalar)
 (pc:s.pc=P.address .loop)(h:Parent (q*m+rest) q A F T rest stack depth s)
 (metadata:s.natHeap (F-1)=some tapeEnd)(live:T < tapeEnd)
 (printed:Printed T (Instruction.record q (.macro a (.shear d src ne c hc))).data s)
 (data:Present A W (2^(q*m+rest)) f s)
 (recordEnd:T+(Instruction.record q (.macro a (.shear d src ne c hc))).data.length ≤ B)
 (width:m+1 ≤ B)(extent:A+W*2^(q*m+rest) ≤ F)(pool:F ≤ B)(base:3 ≤ A)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s)(code:P.program.length ≤ B):
 ∃u,∃g:Fin W→Fin (2^(q*m+rest))→Scalar,
 BoundedRuns P.program n x B s (10*2^(q*m+rest)+4*(q*m+rest)+c.val+102) u ∧
 u.pc=P.address .loop ∧ Parent (q*m+rest) q A F
  (T+(Instruction.record q (.macro a (.shear d src ne c hc))).data.length) rest stack depth u ∧
 Present A W (2^(q*m+rest)) g u ∧
 arrayValues q rest g=(semantic q rest (.macro a (.shear d src ne c hc))).mulVec (arrayValues q rest f) ∧
 Frame A (2^(q*m+rest)) F s u ∧ UniformBinaryCStageMachine.Constants u ∧
 (UniformRecursivePreparedValues.Prepared2 f→UniformRecursivePreparedValues.Prepared2 g):=by
 let di:=roleMap ((fixedBlock a).embedding d)
 let si:=roleMap ((fixedBlock a).embedding src)
 have neq:di≠si:=fun he=>ne ((fixedBlock a).embedding.injective (roleMap.injective he))
 have recordEq:=UniformNativeHandlerSemantics.scalar_record q a d src ne c hc
 change UniformNativeScalarRecordMachine.shearRecord q m di si c=_ at recordEq
 have tableEnd:T+8 ≤ B:=by simpa only [Instruction.record,macroRecord,Record.data_length,List.length_nil,Nat.add_zero] using recordEnd
 have bank:Printed T (UniformNativeScalarRecordMachine.shearRecord q m di si c).data s:=by
  rw [recordEq];exact printed
 obtain ⟨u,t,run,up,out,ptr,cf,sf⟩:=UniformRecursiveNativeRecords.scalar_loop q m (q*m+rest) A T F tapeEnd B n x
  di si neq c f s pc h.cursor h.nativeBase h.nativeBits h.frontier h.one metadata live bank data
  bound code tableEnd width (extent.trans pool)
 let g:=UniformFixedNetworkShearChildMachine.shearValues di si (UniformFixedCoefficientCodec.decode c) f
 have fr:Frame A (2^(q*m+rest)) F s u:=scalar_frame cf sf
 refine ⟨u,g,run,up,?_,out,?_,fr,fr.constants base extent constants,UniformRecursivePreparedValues.shear di si _ f⟩
 · have lengthEq:(Instruction.record q (.macro a (.shear d src ne c hc))).data.length=8:=rfl
   rw [lengthEq];exact UniformRecursiveNativeParent.scalar_parent h ptr cf sf
 · exact (UniformNativeHandlerSemantics.scalar_values q rest a d src ne c hc f).symm


theorem exchange_prepared (n B T tapeEnd A F q rest stack depth:ℕ)(x:Fin n→ℂ)
 (s:State)(f:Fin W→Fin (2^(q*m+rest))→Scalar)
 (pc:s.pc=P.address .loop)(h:Parent (q*m+rest) q A F T rest stack depth s)
 (metadata:s.natHeap (F-1)=some tapeEnd)(live:T < tapeEnd)
 (printed:Printed T (Instruction.record q .exchange).data s)(data:Present A W (2^(q*m+rest)) f s)
 (recordEnd:T+(Instruction.record q .exchange).data.length ≤ B)(width:m+1 ≤ B)
 (extent:A+W*2^(q*m+rest) ≤ F)(pool:F ≤ B)(base:3 ≤ A)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s)(code:P.program.length ≤ B):
 ∃u,∃g:Fin W→Fin (2^(q*m+rest))→Scalar,
 BoundedRuns P.program n x B s
  ((10*2^(q*m+rest)+21)*UniformNativeHandlerSemantics.actualPairs.length+4*(q*m+rest)+99) u ∧
 u.pc=P.address .loop ∧ Parent (q*m+rest) q A F
  (T+(Instruction.record q .exchange).data.length) rest stack depth u ∧
 Present A W (2^(q*m+rest)) g u ∧
 arrayValues q rest g=(semantic q rest .exchange).mulVec (arrayValues q rest f) ∧
 Frame A (2^(q*m+rest)) F s u ∧ UniformBinaryCStageMachine.Constants u ∧
 (UniformRecursivePreparedValues.Prepared2 f→UniformRecursivePreparedValues.Prepared2 g):=by
 have recordEq:=UniformNativeHandlerSemantics.exchange_record q
 change UniformNativeExchangeRecordMachine.record q m UniformNativeHandlerSemantics.actualPairs=_ at recordEq
 have lengthEq:=congrArg (fun r:Record=>r.data.length) recordEq
 have bank:Printed T (UniformNativeExchangeRecordMachine.record q m UniformNativeHandlerSemantics.actualPairs).data s:=by
  rw [recordEq];exact printed
 have endBound:T+8+4*UniformNativeHandlerSemantics.actualPairs.length ≤ B:=by
  rw [←lengthEq,UniformNativeExchangeRecordMachine.record_length] at recordEnd
  simpa only [Nat.add_assoc] using recordEnd
 have pos:0 < W:=Nat.two_pow_pos ExplicitSeedBudget.roleBits
 obtain ⟨u,t,run,up,out,ptr,cf,ef⟩:=UniformRecursiveNativeRecords.exchange_loop q m (q*m+rest) A T F tapeEnd B n x
  UniformNativeHandlerSemantics.actualPairs f s pc h.cursor h.nativeBase h.nativeBits h.frontier h.one metadata live
  bank data pos bound code endBound width (extent.trans pool)
 let g:=UniformNativeExchangeRecordMachine.actions UniformNativeHandlerSemantics.actualPairs f
 have fr:Frame A (2^(q*m+rest)) F s u:=exchange_frame cf ef
 refine ⟨u,g,run,up,?_,out,(UniformNativeHandlerSemantics.exchange_values q rest f).symm,fr,
  fr.constants base extent constants,UniformRecursivePreparedValues.exchanges _ f⟩
 have ptr':u.natReg 2850=T+(Instruction.record q .exchange).data.length:=by
  rw [←lengthEq,UniformNativeExchangeRecordMachine.record_length];simpa only [Nat.add_assoc] using ptr
 exact UniformRecursiveNativeParent.exchange_parent h ptr' cf ef


theorem translation_prepared (n B T tapeEnd A F q rest stack depth:ℕ)(x:Fin n→ℂ)
 (s:State)(f:Fin W→Fin (2^(q*m+rest))→Scalar)
 (pc:s.pc=P.address .loop)(h:Parent (q*m+rest) q A F T rest stack depth s)
 (metadata:s.natHeap (F-1)=some tapeEnd)(live:T < tapeEnd)
 (printed:Printed T (Instruction.record q .translation).data s)(data:Present A W (2^(q*m+rest)) f s)
 (recordEnd:T+(Instruction.record q .translation).data.length ≤ F)
 (width:m+1 ≤ B)(extent:A+W*2^(q*m+rest) ≤ F)(pool:F+5*2^(q*m+rest) ≤ B)
 (square:(2^(q*m+rest))^2 ≤ B)(base:3 ≤ A)(qp:1 ≤ q)(rp:rest < m)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s)(code:P.program.length ≤ B):
 ∃u,∃g:Fin W→Fin (2^(q*m+rest))→Scalar,
 BoundedRuns P.program n x B s
  (UniformNativeYRecordMachine.runtime q m rest (q*m+rest) UniformNativeHandlerSemantics.actualDirections.length+51) u ∧
 u.pc=P.address .loop ∧ Parent (q*m+rest) q A F
  (T+(Instruction.record q .translation).data.length) rest stack depth u ∧
 Present A W (2^(q*m+rest)) g u ∧
 arrayValues q rest g=(semantic q rest .translation).mulVec (arrayValues q rest f) ∧
 Frame A (2^(q*m+rest)) F s u ∧ UniformBinaryCStageMachine.Constants u ∧
 (UniformRecursivePreparedValues.Prepared2 f→UniformRecursivePreparedValues.Prepared2 g):=by
 have recordEq:=UniformNativeHandlerSemantics.translation_record q
 change UniformNativeYRecordMachine.record q m UniformNativeHandlerSemantics.actualDirections=_ at recordEq
 have lengthEq:=congrArg (fun z:Record=>z.data.length) recordEq
 have bank:Printed T (UniformNativeYRecordMachine.record q m UniformNativeHandlerSemantics.actualDirections).data s:=by
  rw [recordEq];exact printed
 have m2:2 ≤ m:=by norm_num [m,ExplicitSeedBudget.m]
 have ex:q*(m+rest) ≤ 2*(q*m+rest):=by
  have mul:=Nat.mul_le_mul_left q (Nat.le_of_lt rp)
  nlinarith
 have padded:2^(q*(m+rest)) ≤ B:=by
  apply le_trans (Nat.pow_le_pow_right (by decide:1 ≤ (2:ℕ)) ex)
  simpa only [Nat.mul_comm 2 (q*m+rest),pow_mul] using square
 have q2:2*q ≤ q*m+rest:=by nlinarith
 have tableSmall:2^q*2^q ≤ 2^(q*m+rest):=by
  rw [←pow_add]
  exact Nat.pow_le_pow_right (by decide:1 ≤ (2:ℕ)) (by omega)
 have sourceBefore:T+(UniformNativeYRecordMachine.record q m UniformNativeHandlerSemantics.actualDirections).data.length ≤ F+3*2^(q*m+rest):=by
  rw [lengthEq];omega
 have tableEnd:F+3*2^(q*m+rest)+2^q*2^q ≤ B:=by omega
 obtain ⟨u,t,a,run,up,out,ptr,cf,rf,yf⟩:=UniformRecursiveNativeRecords.translation_loop q m rest (q*m+rest)
  A (F+4*2^(q*m+rest)) (F+3*2^(q*m+rest)) T F tapeEnd B n x
  UniformNativeHandlerSemantics.actualDirections f s pc h.cursor h.nativeBase h.nativeBits h.nativeRest rfl qp padded
  h.volume rfl h.table h.frontier h.one metadata live bank data bound code sourceBefore
  (by change A+W*2^(q*m+rest) ≤ F+4*2^(q*m+rest);omega) tableEnd
  (by change F+4*2^(q*m+rest)+2^(q*m+rest) ≤ B;omega) width
 let g:=UniformNativeYRecordMachine.actions q m (q*m+rest) UniformNativeHandlerSemantics.actualDirections f
 have fr:Frame A (2^(q*m+rest)) F s u:=translation_frame cf rf yf
 refine ⟨u,g,run,up,?_,out,(UniformNativeHandlerSemantics.translation_values q rest f).symm,fr,
  fr.constants base extent constants,UniformRecursivePreparedValues.translations _ f⟩
 have ptr':u.natReg 2850=T+(Instruction.record q .translation).data.length:=by
  rw [←lengthEq];exact ptr
 exact UniformRecursiveNativeParent.translation_parent h ptr' cf rf yf


theorem marker_prepared (n B T tapeEnd A F q rest stack depth:ℕ)(x:Fin n→ℂ)
 (i:UniformNativeScheduleSemantics.Instruction)(hi:i=.initial∨∃a,i=.boundary a)
 (s:State)(f:Fin W→Fin (2^(q*m+rest))→Scalar)
 (pc:s.pc=P.address .loop)(h:Parent (q*m+rest) q A F T rest stack depth s)
 (metadata:s.natHeap (F-1)=some tapeEnd)(live:T < tapeEnd)
 (printed:Printed T (Instruction.record q i).data s)(data:Present A W (2^(q*m+rest)) f s)
 (recordEnd:T+(Instruction.record q i).data.length ≤ B)(width:m+1 ≤ B)
 (extent:A+W*2^(q*m+rest) ≤ F)(base:3 ≤ A)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s)(code:P.program.length ≤ B):
 ∃u,∃g:Fin W→Fin (2^(q*m+rest))→Scalar,
 BoundedRuns P.program n x B s
  (6+2*UniformFixedNetworkOpcodeMachine.headCost (Instruction.record q i)+
   UniformRecursiveRecordControl.dispatchCost (Instruction.record q i).opcode) u ∧
 u.pc=P.address .loop ∧ Parent (q*m+rest) q A F
  (T+(Instruction.record q i).data.length) rest stack depth u ∧
 Present A W (2^(q*m+rest)) g u ∧
 arrayValues q rest g=(semantic q rest i).mulVec (arrayValues q rest f) ∧
 Frame A (2^(q*m+rest)) F s u ∧ UniformBinaryCStageMachine.Constants u ∧
 (UniformRecursivePreparedValues.Prepared2 f→UniformRecursivePreparedValues.Prepared2 g):=by
 have good:=marker_good q i hi
 have wb:(Instruction.record q i).width+1 ≤ B:=by
  rcases hi with rfl|⟨a,rfl⟩ <;> exact width
 obtain ⟨u,t,run,up,ptr,cf,mf⟩:=UniformRecursiveNativeRecords.marker_loop T F tapeEnd B n
  (Instruction.record q i) x s pc h.cursor h.frontier h.one metadata live printed good.2 good.1 bound code recordEnd wb
 have values:UniformNativeHandlerSemantics.SemanticPresent A q rest i f u:=by
  rcases hi with rfl|⟨a,rfl⟩
  · exact UniformNativeHandlerSemantics.initial_present A q rest f s t u data cf mf
  · exact UniformNativeHandlerSemantics.boundary_present A q rest a f s t u data cf mf
 obtain ⟨g,gp,gv⟩:=values
 have fr:Frame A (2^(q*m+rest)) F s u:=marker_frame cf mf
 have prepared : UniformRecursivePreparedValues.Prepared2 f→UniformRecursivePreparedValues.Prepared2 g := by
  intro prep i j
  have same : g i j=f i j := Option.some.inj ((gp i j).symm.trans
   ((congrFun mf.scalarHeap _).trans ((congrFun cf.scalarHeap _).trans (data i j))))
  rw [same]
  exact prep i j
 exact ⟨u,g,run,up,UniformRecursiveNativeParent.marker_parent h ptr cf mf,gp,gv,fr,
  fr.constants base extent constants,prepared⟩

end
end ExactFourierCircuits.UniformRecursiveNativeTypedRecords

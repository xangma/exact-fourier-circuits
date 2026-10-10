import DFTModelSavingNativeExchange

set_option autoImplicit false

/-! Exact paired source adapter for the real saving-program Y record. The
charged v2 restore and all variable inline directions are part of the run. -/
namespace ExactFourierCircuits.DFTModelSavingNativeY
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine
open UniformNativeScheduleSemantics DFTModelAffine DFTModelClockControl
open DFTModelAdmissibilityControl DFTModelSavingNativeControl
open DFTModelRecursiveScalarSource (paired paired_lookup)
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursiveResidualEdge (Parent)
open DFTModelSavingNativeExchange (parent_match constants_match)
noncomputable section

theorem dispatch_run (R rest : ℕ) (raw : Tape ℕ) (node : Node.T)
    (h : Handler ChildPort) (opcode : raw.look 0 0=3) :
    Code.run (DFTModelSavingRecords.dispatch R) h (rest,(raw,node))=
      (run (DFTModelSavingY.program R) (rest,(raw,node))).pay 49 3 := by
  simp [DFTModelSavingRecords.dispatch,DFTModelSavingRecords.field,
    DFTModelSavingRecords.raw,DFTModelSavingRecords.opcodeTest,
    DFTModelResidualCore.binary,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay,Ty.blank,opcode]
  omega

attribute [local irreducible] DFTModelSavingY.program DFTModelSavingRecords.dispatch

theorem record_source {R width : ℕ} (q : ℕ)
    (ds : List (UniformNativeYRecordMachine.Direction R width)) :
    DFTModelSavingY.RecordSource q ds
      (DFTModelCacheRecords.dataTape (UniformNativeYRecordMachine.record q width ds).data) := by
  intro j hj
  exact dataTape_lookup _ j hj

theorem actual_execution (n B T tapeEnd A F q rest stack depth : ℕ) (x : Fin n→ℂ)
    (s s0 : State) (I : ℂ) (handler : Handler ChildPort)
    (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar) (same : StateMatch s s0)
    (pc : s.pc=UniformRecursiveSavingProgram.address .loop)
    (parent : Parent (q*m+rest) q A F T rest stack depth s)
    (metadata : s.natHeap (F-1)=some tapeEnd) (live : T<tapeEnd)
    (printed : Printed T (Instruction.record q .translation).data s)
    (data : Present A W (2^(q*m+rest)) f s)
    (baseline : Present A W (2^(q*m+rest)) f0 s0)
    (recordEnd : T+(Instruction.record q .translation).data.length≤F) (width : m+1≤B)
    (extent : A+W*2^(q*m+rest)≤F) (pool : F+5*2^(q*m+rest)≤B)
    (square : (2^(q*m+rest))^2≤B) (base : 3≤A) (qp : 1≤q) (rp : rest < m)
    (constants : UniformBinaryCStageMachine.Constants s) (bound : WordBound B s)
    (code : UniformRecursiveSavingProgram.program.length≤B) :
    ∃u u0,
      BoundedRuns UniformRecursiveSavingProgram.program n x B s
        (UniformNativeYRecordMachine.runtime q m rest (q*m+rest)
          UniformNativeHandlerSemantics.actualDirections.length+51) u ∧
      BoundedRuns UniformRecursiveSavingProgram.program n (fun _=>0) B s0
        (UniformNativeYRecordMachine.runtime q m rest (q*m+rest)
          UniformNativeHandlerSemantics.actualDirections.length+51) u0 ∧
      StateMatch u u0 ∧ u.pc=UniformRecursiveSavingProgram.address .loop ∧
      u0.pc=UniformRecursiveSavingProgram.address .loop ∧
      Parent (q*m+rest) q A F (T+(Instruction.record q .translation).data.length) rest stack depth u ∧
      Parent (q*m+rest) q A F (T+(Instruction.record q .translation).data.length) rest stack depth u0 ∧
      Present A W (2^(q*m+rest))
        (UniformNativeYRecordMachine.actions q m (q*m+rest) UniformNativeHandlerSemantics.actualDirections f) u ∧
      Present A W (2^(q*m+rest))
        (UniformNativeYRecordMachine.actions q m (q*m+rest) UniformNativeHandlerSemantics.actualDirections f0) u0 ∧
      UniformRecursiveNativeTypedRecords.Frame A (2^(q*m+rest)) F s u ∧
      UniformRecursiveNativeTypedRecords.Frame A (2^(q*m+rest)) F s0 u0 ∧
      UniformBinaryCStageMachine.Constants u ∧ UniformBinaryCStageMachine.Constants u0 ∧
      (Code.run (DFTModelSavingRecords.dispatch W) handler
        (rest,(DFTModelCacheRecords.dataTape (Instruction.record q .translation).data,
          ((q*m+rest,I),paired f f0)))).val=
        ((q*m+rest,I),paired
          (UniformNativeYRecordMachine.actions q m (q*m+rest) UniformNativeHandlerSemantics.actualDirections f)
          (UniformNativeYRecordMachine.actions q m (q*m+rest) UniformNativeHandlerSemantics.actualDirections f0)) ∧
      (Code.run (DFTModelSavingRecords.dispatch W) handler
        (rest,(DFTModelCacheRecords.dataTape (Instruction.record q .translation).data,
          ((q*m+rest,I),paired f f0)))).valid := by
  have eqr:=UniformNativeHandlerSemantics.translation_record q
  change UniformNativeYRecordMachine.record q m UniformNativeHandlerSemantics.actualDirections=_ at eqr
  have bank : Printed T (UniformNativeYRecordMachine.record q m UniformNativeHandlerSemantics.actualDirections).data s := by
    rw [eqr];exact printed
  have bank0 : Printed T (UniformNativeYRecordMachine.record q m UniformNativeHandlerSemantics.actualDirections).data s0 := by
    intro j hj;rw [same.natHeap];exact bank j hj
  have m2 : 2 ≤ m:=by norm_num [m,ExplicitSeedBudget.m]
  have exponent : q*(m+rest)≤2*(q*m+rest) := by
    have mul:=Nat.mul_le_mul_left q (Nat.le_of_lt rp)
    nlinarith
  have padded : 2^(q*(m+rest))≤B := by
    apply le_trans (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) exponent)
    simpa only [Nat.mul_comm 2 (q*m+rest),pow_mul] using square
  have small : 2^q*2^q≤2^(q*m+rest) := by
    rw [←pow_add]
    exact Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) (by nlinarith)
  have before : T+(UniformNativeYRecordMachine.record q m UniformNativeHandlerSemantics.actualDirections).data.length≤F+3*2^(q*m+rest) := by
    rw [eqr];omega
  have tableEnd : F+3*2^(q*m+rest)+2^q*2^q≤B := by omega
  obtain ⟨u,t,a,exec,up,out,ptr,cf,rf,yf⟩:=UniformRecursiveNativeRecords.translation_loop
    q m rest (q*m+rest) A (F+4*2^(q*m+rest)) (F+3*2^(q*m+rest)) T F tapeEnd B n x
    UniformNativeHandlerSemantics.actualDirections f s pc parent.cursor parent.nativeBase parent.nativeBits
    parent.nativeRest rfl qp padded parent.volume rfl parent.table parent.frontier parent.one metadata live
    bank data bound code before (by change A+W*2^(q*m+rest)≤F+4*2^(q*m+rest);omega)
    tableEnd (by change F+4*2^(q*m+rest)+2^(q*m+rest)≤B;omega) width
  have parent0:=parent_match same parent
  obtain ⟨u0,t0,a0,exec0,up0,out0,ptr0,cf0,rf0,yf0⟩:=UniformRecursiveNativeRecords.translation_loop
    q m rest (q*m+rest) A (F+4*2^(q*m+rest)) (F+3*2^(q*m+rest)) T F tapeEnd B n (fun _=>0)
    UniformNativeHandlerSemantics.actualDirections f0 s0 (same.pc.trans pc) parent0.cursor parent0.nativeBase parent0.nativeBits
    parent0.nativeRest rfl qp padded parent0.volume rfl parent0.table parent0.frontier parent0.one
    (by rw [same.natHeap];exact metadata) live bank0 baseline (same.wordBound bound) code before
    (by change A+W*2^(q*m+rest)≤F+4*2^(q*m+rest);omega)
    tableEnd (by change F+4*2^(q*m+rest)+2^(q*m+rest)≤B;omega) width
  have next : u.natReg 2850=T+(Instruction.record q .translation).data.length := by rw [←eqr];exact ptr
  have next0 : u0.natReg 2850=T+(Instruction.record q .translation).data.length := by rw [←eqr];exact ptr0
  have fr:=UniformRecursiveNativeTypedRecords.translation_frame (F:=F) cf rf yf
  have fr0:=UniformRecursiveNativeTypedRecords.translation_frame (F:=F) cf0 rf0 yf0
  have opcode : (DFTModelCacheRecords.dataTape (Instruction.record q .translation).data).look 0 0=3 := by
    rw [←eqr,dataTape_lookup _ 0 (by rw [UniformNativeYRecordMachine.record_length];omega)]
    rfl
  have dr:=dispatch_run W rest _ ((q*m+rest,I),paired f f0) handler opcode
  refine ⟨u,u0,exec,exec0,paired_runs exec exec0 same,up,up0,
    UniformRecursiveNativeParent.translation_parent parent next cf rf yf,
    UniformRecursiveNativeParent.translation_parent parent0 next0 cf0 rf0 yf0,out,out0,fr,fr0,
    fr.constants base extent constants,
    fr0.constants base extent (constants_match same constants),?_,?_⟩
  · rw [dr]
    change (run (DFTModelSavingY.program W) (rest,(_,((q*m+rest,I),paired f f0)))).val=_
    rw [←eqr]
    exact DFTModelSavingY.program_value q rest (q*m+rest) I _ UniformNativeHandlerSemantics.actualDirections
      (record_source q _) f f0 (Nat.two_pow_pos ExplicitSeedBudget.roleBits) rfl qp
  · rw [dr]
    change (run (DFTModelSavingY.program W) _).valid
    exact DFTModelSavingY.program_valid _ _

theorem dispatch_bounds (q rest B : ℕ) (I : ℂ) (handler : Handler ChildPort)
    (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar) (qp : 1≤q) (rp : rest < m)
    (extent : W*2^(q*m+rest)≤B)
    (recordEnd : (Instruction.record q .translation).data.length≤B)
    (square : (2^(q*m+rest))^2≤B) :
    (Code.run (DFTModelSavingRecords.dispatch W) handler
      (rest,(DFTModelCacheRecords.dataTape (Instruction.record q .translation).data,
        ((q*m+rest,I),paired f f0)))).work≤
      (32*(W+1)+49)*(UniformNativeYRecordMachine.runtime q m rest (q*m+rest)
        UniformNativeHandlerSemantics.actualDirections.length+51) ∧
    (Code.run (DFTModelSavingRecords.dispatch W) handler
      (rest,(DFTModelCacheRecords.dataTape (Instruction.record q .translation).data,
        ((q*m+rest,I),paired f f0)))).peak≤4*B+2 := by
  have eqr:=UniformNativeHandlerSemantics.translation_record q
  change UniformNativeYRecordMachine.record q m UniformNativeHandlerSemantics.actualDirections=_ at eqr
  have opcode : (DFTModelCacheRecords.dataTape (Instruction.record q .translation).data).look 0 0=3 := by
    rw [←eqr,dataTape_lookup _ 0 (by rw [UniformNativeYRecordMachine.record_length];omega)]
    rfl
  rw [dispatch_run W rest _ _ handler opcode,←eqr]
  have pos : 0<W:=Nat.two_pow_pos ExplicitSeedBudget.roleBits
  have source:=record_source q UniformNativeHandlerSemantics.actualDirections
  constructor
  · change (run (DFTModelSavingY.program W)
      (DFTModelSavingY.input rest (q*m+rest) I _ (paired f f0))).work+49≤_
    have h:=DFTModelSavingY.program_work q rest (q*m+rest) I _ UniformNativeHandlerSemantics.actualDirections
      source f f0 pos rfl qp
    let runtime:=UniformNativeYRecordMachine.runtime q m rest (q*m+rest)
      UniformNativeHandlerSemantics.actualDirections.length
    have mul:=Nat.mul_le_mul_left (32*(W+1)) (show runtime≤runtime+51 by omega)
    have extra:=Nat.mul_le_mul_left 49 (show 1≤runtime+51 by omega)
    simp only [Nat.mul_one] at extra
    calc
      _≤32*(W+1)*runtime+49:=Nat.add_le_add_right h 49
      _≤32*(W+1)*(runtime+51)+49*(runtime+51):=Nat.add_le_add mul extra
      _=_:=by rw [Nat.add_mul]
  · change max (run (DFTModelSavingY.program W)
      (DFTModelSavingY.input rest (q*m+rest) I _ (paired f f0))).peak 3≤4*B+2
    have m2 : 2 ≤ m:=by norm_num [m,ExplicitSeedBudget.m]
    have exponent : q*(m+rest)≤2*(q*m+rest) := by
      have mul:=Nat.mul_le_mul_left q (Nat.le_of_lt rp)
      nlinarith
    have padded : 2^(q*(m+rest))≤B := by
      apply le_trans (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) exponent)
      simpa only [Nat.mul_comm 2 (q*m+rest),pow_mul] using square
    have small : 2^q*2^q≤B := by
      rw [←pow_add]
      apply le_trans (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) (show q+q≤2*(q*m+rest) by nlinarith))
      simpa only [Nat.mul_comm 2 (q*m+rest),pow_mul] using square
    have endFit : 8+(m+1)*UniformNativeHandlerSemantics.actualDirections.length≤B := by
      rw [←eqr,UniformNativeYRecordMachine.record_length] at recordEnd
      exact recordEnd
    exact max_le (DFTModelSavingY.program_peak q rest (q*m+rest) B I _
      UniformNativeHandlerSemantics.actualDirections source f f0 pos rfl qp extent endFit padded small) (by omega)

end
end ExactFourierCircuits.DFTModelSavingNativeY

import DFTModelSavingRecords
import DFTModelSavingNativeControl
import UniformRecursiveNativeTypedRecords

set_option autoImplicit false

/-! The genuine same-program exchange record and its one paired typed run.
No canonical flag pattern or produced output bank is an entry premise. -/
namespace ExactFourierCircuits.DFTModelSavingNativeExchange
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine
open UniformNativeScheduleSemantics DFTModelAffine DFTModelClockControl
open DFTModelAdmissibilityControl DFTModelSavingNativeControl
open DFTModelRecursiveScalarSource (paired paired_lookup)
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursiveResidualEdge (Parent)
noncomputable section

theorem dispatch_run (R rest : ℕ) (raw : Tape ℕ) (node : Node.T)
    (h : Handler ChildPort) (opcode : raw.look 0 0=4) :
    Code.run (DFTModelSavingRecords.dispatch R) h (rest,(raw,node))=
      (run (DFTModelRecursiveExchange.program R) (raw,node)).pay 71 4 := by
  simp [DFTModelSavingRecords.dispatch,DFTModelSavingRecords.field,
    DFTModelSavingRecords.raw,DFTModelSavingRecords.opcodeTest,
    DFTModelSavingRecords.exchangeArgs,DFTModelSavingRecords.initial,
    DFTModelResidualCore.binary,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay,Ty.blank,opcode]
  omega

attribute [local irreducible] DFTModelRecursiveExchange.program DFTModelSavingRecords.dispatch

theorem recordTape_eq {R : ℕ} (q w : ℕ)
    (ps : List (UniformNativeExchangeRecordMachine.Pair R)) :
    DFTModelCacheRecords.dataTape (UniformNativeExchangeRecordMachine.record q w ps).data=
      DFTModelRecursiveExchange.recordTape q w ps := by
  apply DFTModelSavingY.tape_ext (a:=DFTModelCacheRecords.dataTape
    (UniformNativeExchangeRecordMachine.record q w ps).data)
    (b:=DFTModelRecursiveExchange.recordTape q w ps) 0 (by rfl)
  intro j
  by_cases hj : j<(UniformNativeExchangeRecordMachine.record q w ps).data.length
  · rw [dataTape_lookup _ j hj,Tape.look_of_lt _ _ hj]
    rfl
  · rw [Tape.look_of_le _ _ (by change (UniformNativeExchangeRecordMachine.record q w ps).data.length≤j;omega),
      Tape.look_of_le _ _ (by change (UniformNativeExchangeRecordMachine.record q w ps).data.length≤j;omega)]

theorem parent_match {k q A F T rest stack depth : ℕ} {s s0 : State}
    (same : StateMatch s s0) (h : Parent k q A F T rest stack depth s) :
    Parent k q A F T rest stack depth s0 :=
  UniformRecursiveNativeParent.parent_congr h
    (by rw [same.natReg];exact h.cursor) (fun j _=>congrFun same.natReg j)

theorem constants_match {s s0 : State} (same : StateMatch s s0)
    (h : UniformBinaryCStageMachine.Constants s) : UniformBinaryCStageMachine.Constants s0 := by
  constructor
  · obtain ⟨z,hz,m⟩:=(same.scalarHeap 1).left h.1
    rw [←m.eq_of_prepared rfl] at hz
    exact hz
  · obtain ⟨z,hz,m⟩:=(same.scalarHeap 2).left h.2
    rw [←m.eq_of_prepared rfl] at hz
    exact hz

/-- Genuine loop entry and return, retaining the parent and both actual tag
patterns. The arbitrary internal handler is unreachable for this opcode. -/
theorem actual_execution (n B T tapeEnd A F q rest stack depth : ℕ) (x : Fin n→ℂ)
    (s s0 : State) (I : ℂ) (handler : Handler ChildPort)
    (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar) (same : StateMatch s s0)
    (pc : s.pc=UniformRecursiveSavingProgram.address .loop)
    (parent : Parent (q*m+rest) q A F T rest stack depth s)
    (metadata : s.natHeap (F-1)=some tapeEnd) (live : T<tapeEnd)
    (printed : Printed T (Instruction.record q .exchange).data s)
    (data : Present A W (2^(q*m+rest)) f s)
    (baseline : Present A W (2^(q*m+rest)) f0 s0)
    (recordEnd : T+(Instruction.record q .exchange).data.length≤B) (width : m+1≤B)
    (extent : A+W*2^(q*m+rest)≤F) (pool : F≤B) (base : 3≤A)
    (constants : UniformBinaryCStageMachine.Constants s) (bound : WordBound B s)
    (code : UniformRecursiveSavingProgram.program.length≤B) :
    ∃u u0,
      BoundedRuns UniformRecursiveSavingProgram.program n x B s
        ((10*2^(q*m+rest)+21)*UniformNativeHandlerSemantics.actualPairs.length+4*(q*m+rest)+99) u ∧
      BoundedRuns UniformRecursiveSavingProgram.program n (fun _=>0) B s0
        ((10*2^(q*m+rest)+21)*UniformNativeHandlerSemantics.actualPairs.length+4*(q*m+rest)+99) u0 ∧
      StateMatch u u0 ∧ u.pc=UniformRecursiveSavingProgram.address .loop ∧
      u0.pc=UniformRecursiveSavingProgram.address .loop ∧
      Parent (q*m+rest) q A F (T+(Instruction.record q .exchange).data.length) rest stack depth u ∧
      Parent (q*m+rest) q A F (T+(Instruction.record q .exchange).data.length) rest stack depth u0 ∧
      Present A W (2^(q*m+rest)) (UniformNativeExchangeRecordMachine.actions UniformNativeHandlerSemantics.actualPairs f) u ∧
      Present A W (2^(q*m+rest)) (UniformNativeExchangeRecordMachine.actions UniformNativeHandlerSemantics.actualPairs f0) u0 ∧
      UniformRecursiveNativeTypedRecords.Frame A (2^(q*m+rest)) F s u ∧
      UniformRecursiveNativeTypedRecords.Frame A (2^(q*m+rest)) F s0 u0 ∧
      UniformBinaryCStageMachine.Constants u ∧ UniformBinaryCStageMachine.Constants u0 ∧
      (Code.run (DFTModelSavingRecords.dispatch W) handler
        (rest,(DFTModelCacheRecords.dataTape (Instruction.record q .exchange).data,
          ((q*m+rest,I),paired f f0)))).val=
        ((q*m+rest,I),paired
          (UniformNativeExchangeRecordMachine.actions UniformNativeHandlerSemantics.actualPairs f)
          (UniformNativeExchangeRecordMachine.actions UniformNativeHandlerSemantics.actualPairs f0)) ∧
      (Code.run (DFTModelSavingRecords.dispatch W) handler
        (rest,(DFTModelCacheRecords.dataTape (Instruction.record q .exchange).data,
          ((q*m+rest,I),paired f f0)))).valid := by
  have eqr:=UniformNativeHandlerSemantics.exchange_record q
  change UniformNativeExchangeRecordMachine.record q m UniformNativeHandlerSemantics.actualPairs=_ at eqr
  have lengths:=congrArg (fun r : Record=>r.data.length) eqr
  have endBound : T+8+4*UniformNativeHandlerSemantics.actualPairs.length≤B := by
    rw [←lengths,UniformNativeExchangeRecordMachine.record_length] at recordEnd
    simpa only [Nat.add_assoc] using recordEnd
  have bank : Printed T (UniformNativeExchangeRecordMachine.record q m UniformNativeHandlerSemantics.actualPairs).data s := by
    rw [eqr];exact printed
  have bank0 : Printed T (UniformNativeExchangeRecordMachine.record q m UniformNativeHandlerSemantics.actualPairs).data s0 := by
    intro j hj;rw [same.natHeap];exact bank j hj
  have pos : 0<W:=Nat.two_pow_pos ExplicitSeedBudget.roleBits
  obtain ⟨u,t,exec,up,out,ptr,cf,ef⟩:=UniformRecursiveNativeRecords.exchange_loop
    q m (q*m+rest) A T F tapeEnd B n x UniformNativeHandlerSemantics.actualPairs f s pc
    parent.cursor parent.nativeBase parent.nativeBits parent.frontier parent.one metadata live
    bank data pos bound code endBound width (extent.trans pool)
  have parent0:=parent_match same parent
  obtain ⟨u0,t0,exec0,up0,out0,ptr0,cf0,ef0⟩:=UniformRecursiveNativeRecords.exchange_loop
    q m (q*m+rest) A T F tapeEnd B n (fun _=>0) UniformNativeHandlerSemantics.actualPairs f0 s0
    (same.pc.trans pc) parent0.cursor parent0.nativeBase parent0.nativeBits parent0.frontier parent0.one
    (by rw [same.natHeap];exact metadata) live bank0 baseline pos (same.wordBound bound)
    code endBound width (extent.trans pool)
  have next : u.natReg 2850=T+(Instruction.record q .exchange).data.length := by
    rw [←lengths,UniformNativeExchangeRecordMachine.record_length]
    simpa only [Nat.add_assoc] using ptr
  have next0 : u0.natReg 2850=T+(Instruction.record q .exchange).data.length := by
    rw [←lengths,UniformNativeExchangeRecordMachine.record_length]
    simpa only [Nat.add_assoc] using ptr0
  have fr:=UniformRecursiveNativeTypedRecords.exchange_frame (F:=F) cf ef
  have fr0:=UniformRecursiveNativeTypedRecords.exchange_frame (F:=F) cf0 ef0
  have opcode : (DFTModelCacheRecords.dataTape (Instruction.record q .exchange).data).look 0 0=4 := by
    rw [←eqr,dataTape_lookup _ 0 (by rw [UniformNativeExchangeRecordMachine.record_length];omega)]
    rfl
  have dr:=dispatch_run W rest _ ((q*m+rest,I),paired f f0) handler opcode
  refine ⟨u,u0,exec,exec0,paired_runs exec exec0 same,up,up0,
    UniformRecursiveNativeParent.exchange_parent parent next cf ef,
    UniformRecursiveNativeParent.exchange_parent parent0 next0 cf0 ef0,out,out0,fr,fr0,
    fr.constants base extent constants,
    fr0.constants base extent (constants_match same constants),?_,?_⟩
  · rw [dr]
    change (run (DFTModelRecursiveExchange.program W) (_,((q*m+rest,I),paired f f0))).val=_
    rw [←eqr,recordTape_eq]
    exact DFTModelRecursiveExchange.program_value q m UniformNativeHandlerSemantics.actualPairs (by positivity) f f0 (q*m+rest) I
  · rw [dr]
    change (run (DFTModelRecursiveExchange.program W)
      (DFTModelCacheRecords.dataTape (Instruction.record q .exchange).data,
        ((q*m+rest,I),paired f f0))).valid
    exact DFTModelRecursiveExchange.program_valid _ _ _

theorem dispatch_bounds (q rest k B : ℕ) (I : ℂ) (handler : Handler ChildPort)
    (f f0 : Fin W→Fin (2^k)→Scalar)
    (endFit : 8+4*UniformNativeHandlerSemantics.actualPairs.length≤B)
    (extent : W*2^k≤B) :
    (Code.run (DFTModelSavingRecords.dispatch W) handler
      (rest,(DFTModelCacheRecords.dataTape (Instruction.record q .exchange).data,
        ((k,I),paired f f0)))).work≤
      (20*W+81)*((10*2^k+21)*UniformNativeHandlerSemantics.actualPairs.length+4*k+99) ∧
    (Code.run (DFTModelSavingRecords.dispatch W) handler
      (rest,(DFTModelCacheRecords.dataTape (Instruction.record q .exchange).data,
        ((k,I),paired f f0)))).peak≤B := by
  have eqr:=UniformNativeHandlerSemantics.exchange_record q
  change UniformNativeExchangeRecordMachine.record q m UniformNativeHandlerSemantics.actualPairs=_ at eqr
  have opcode : (DFTModelCacheRecords.dataTape (Instruction.record q .exchange).data).look 0 0=4 := by
    rw [←eqr,dataTape_lookup _ 0 (by rw [UniformNativeExchangeRecordMachine.record_length];omega)]
    rfl
  rw [dispatch_run W rest _ _ handler opcode,←eqr,recordTape_eq]
  have pos : 0<W:=Nat.two_pow_pos ExplicitSeedBudget.roleBits
  constructor
  · change (run (DFTModelRecursiveExchange.program W)
      (DFTModelRecursiveExchange.recordTape q m UniformNativeHandlerSemantics.actualPairs,
        ((k,I),paired f f0))).work+71≤_
    have h:=DFTModelRecursiveExchange.program_native_work q m k UniformNativeHandlerSemantics.actualPairs f f0 I
    have bigger:=Nat.mul_le_mul_left (20*W+10)
      (show (10*2^k+21)*UniformNativeHandlerSemantics.actualPairs.length+4*k+50≤
        (10*2^k+21)*UniformNativeHandlerSemantics.actualPairs.length+4*k+99 by omega)
    nlinarith
  · change max (run (DFTModelRecursiveExchange.program W)
      (DFTModelRecursiveExchange.recordTape q m UniformNativeHandlerSemantics.actualPairs,
        ((k,I),paired f f0))).peak 4≤B
    exact max_le (DFTModelRecursiveExchange.program_peak_bound q m UniformNativeHandlerSemantics.actualPairs
      (by positivity) pos f f0 k B I endFit extent) (by omega)

end
end ExactFourierCircuits.DFTModelSavingNativeExchange

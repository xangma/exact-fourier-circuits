import UniformRecursiveRecordControl
import UniformRecursiveYRestore
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveNativeRecords
open UniformMachine UniformAssembly
open UniformFixedNetworkScheduleMachine (Printed Record)
open UniformFixedNetworkShearChildMachine (Present)
open UniformResidualNativeTranslationMachine (volume)
namespace P
export UniformRecursiveSavingProgram (program address size)
end P
namespace R
export UniformRecursiveParentReturn (start_bound code_bound)
end R
namespace C
export UniformRecursiveRecordControl (ControlFrame ControlChanged read_dispatch_execution targets dispatchCost)
end C
namespace S
export UniformNativeScalarRecordMachine (shearRecord shearRecord_good ScalarFrame scalarProgram)
end S
namespace E
export UniformNativeExchangeRecordMachine (Pair record record_good actions FullFrame program)
end E
namespace Y
export UniformNativeYRecordMachine (Direction record record_good actions FullFrame program runtime)
end Y
noncomputable section

lemma vector_scalar (pc a b c d e f g:ℕ)(h:pc=(![a,b,c,d,e,f,g]) 1):pc=b:=h
lemma vector_exchange (pc a b c d e f g:ℕ)(h:pc=(![a,b,c,d,e,f,g]) 4):pc=e:=h
lemma vector_translation (pc a b c d e f g:ℕ)(h:pc=(![a,b,c,d,e,f,g]) 3):pc=d:=h
lemma vector_marker2 (pc a b c d e f g:ℕ)(h:pc=(![a,b,c,d,e,f,g]) 2):pc=c:=h
lemma vector_marker6 (pc a b c d e f g:ℕ)(h:pc=(![a,b,c,d,e,f,g]) 6):pc=g:=h
lemma scalar_pc (pc:ℕ)(h:pc=C.targets 1):pc=P.address .scalar:=
 vector_scalar pc (P.address .residualMark) (P.address .scalar) (P.address .marker)
  (P.address .yRestore) (P.address .exchange) (P.address .paddingInit) (P.address .marker) h
lemma exchange_pc (pc:ℕ)(h:pc=C.targets 4):pc=P.address .exchange:=
 vector_exchange pc (P.address .residualMark) (P.address .scalar) (P.address .marker)
  (P.address .yRestore) (P.address .exchange) (P.address .paddingInit) (P.address .marker) h
lemma translation_pc (pc:ℕ)(h:pc=C.targets 3):pc=P.address .yRestore:=
 vector_translation pc (P.address .residualMark) (P.address .scalar) (P.address .marker)
  (P.address .yRestore) (P.address .exchange) (P.address .paddingInit) (P.address .marker) h
lemma marker2_pc (pc:ℕ)(h:pc=C.targets 2):pc=P.address .marker:=
 vector_marker2 pc (P.address .residualMark) (P.address .scalar) (P.address .marker)
  (P.address .yRestore) (P.address .exchange) (P.address .paddingInit) (P.address .marker) h
lemma marker6_pc (pc:ℕ)(h:pc=C.targets 6):pc=P.address .marker:=
 vector_marker6 pc (P.address .residualMark) (P.address .scalar) (P.address .marker)
  (P.address .yRestore) (P.address .exchange) (P.address .paddingInit) (P.address .marker) h
lemma printed_control {s t:State}{A:ℕ}{data:List ℕ}(fr:C.ControlFrame s t)(bank:Printed A data s):Printed A data t:=by
 intro j hj;rw [fr.natHeap];exact bank j hj
lemma present_control {s t:State}{A R V:ℕ}{f:Fin R→Fin V→Scalar}(fr:C.ControlFrame s t)(data:Present A R V f s):Present A R V f t:=by
 intro i j;rw [fr.scalarHeap];exact data i j

/-- Actual raw opcode1 from the parent loop through scalar execution and back.
The intermediate state witnesses the complete control and data frame. -/
theorem scalar_loop {roles:ℕ}(q w k A T work tapeEnd B n:ℕ)(x:Fin n→ℂ)
 (d source:Fin roles)(ne:d≠source)(c:Fin 5)(f:Fin roles→Fin (2^k)→Scalar)(s:State)
 (pc:s.pc=P.address .loop)(ptr:s.natReg 2850=T)(base:s.natReg 3300=A)(native:s.natReg 5300=k)
 (workHeader:s.natReg 4123=work)(one:s.natReg 4153=1)(metadata:s.natHeap (work-1)=some tapeEnd)(live:T<tapeEnd)
 (bank:Printed T (S.shearRecord q w d source c).data s)(data:Present A roles (2^k) f s)
 (bound:WordBound B s)(code:P.program.length ≤ B)(tableEnd:T+8 ≤ B)(width:w+1 ≤ B)(extent:A+roles*2^k ≤ B):∃u t,
 BoundedRuns P.program n x B s (10*2^k+4*k+c.val+102) u ∧ u.pc=P.address .loop ∧
 Present A roles (2^k) (UniformFixedNetworkShearChildMachine.shearValues d source (UniformFixedCoefficientCodec.decode c) f) u ∧
 u.natReg 2850=T+8 ∧ C.ControlFrame s t ∧
 S.ScalarFrame (UniformFixedNetworkShearChildMachine.roleBase A (2^k) d.val) (2^k) t u:=by
 obtain ⟨t,controlRun,tp,fields,_,_,fr⟩:=C.read_dispatch_execution work T tapeEnd B n (S.shearRecord q w d source c) x s
  pc workHeader ptr one metadata live bank (S.shearRecord_good q w d source c) bound tableEnd width code
 have fi:(⟨(S.shearRecord q w d source c).opcode,(S.shearRecord_good q w d source c).1⟩:Fin 7)=1:=Fin.ext (by rfl)
 have sp:t.pc=P.address .scalar:=scalar_pc t.pc (tp.trans (congrArg C.targets fi))
 have ba:t.natReg 3300=A:=(fr.natReg _ (by unfold C.ControlChanged;omega)).trans base
 have nk:t.natReg 5300=k:=(fr.natReg _ (by unfold C.ControlChanged;omega)).trans native
 obtain ⟨u,run,up,out,done,sf⟩:=UniformRecursiveNativeEntries.UniformNativeScalarRecordMachine.entry q w k A T B n x
  d source ne c f t sp fields.cursor ba nk (printed_control fr bank) (present_control fr data) controlRun.final_bound
  (R.code_bound .scalar S.scalarProgram.length B rfl code) (R.start_bound .loop B code) tableEnd width extent
 refine ⟨u,t,?_,up,out,done,fr,sf⟩
 convert controlRun.trans run using 1
 simp [UniformFixedNetworkOpcodeMachine.headCost,UniformNativeScalarRecordMachine.shearRecord,C.dispatchCost]
 omega

/-- Real variable pair records are read and exchanged on all native bits. -/
theorem exchange_loop {roles:ℕ}(q w k A T work tapeEnd B n:ℕ)(x:Fin n→ℂ)(pairs:List (E.Pair roles))
 (f:Fin roles→Fin (2^k)→Scalar)(s:State)
 (pc:s.pc=P.address .loop)(ptr:s.natReg 2850=T)(base:s.natReg 3300=A)(native:s.natReg 5300=k)
 (workHeader:s.natReg 4123=work)(one:s.natReg 4153=1)(metadata:s.natHeap (work-1)=some tapeEnd)(live:T<tapeEnd)
 (bank:Printed T (E.record q w pairs).data s)(data:Present A roles (2^k) f s)(positive:0<roles)
 (bound:WordBound B s)(code:P.program.length ≤ B)(tableEnd:T+8+4*pairs.length ≤ B)(width:w+1 ≤ B)(extent:A+roles*2^k ≤ B):∃u t,
 BoundedRuns P.program n x B s ((10*2^k+21)*pairs.length+4*k+99) u ∧ u.pc=P.address .loop ∧
 Present A roles (2^k) (E.actions pairs f) u ∧ u.natReg 2850=T+8+4*pairs.length ∧
 C.ControlFrame s t ∧ E.FullFrame A (roles*2^k) t u:=by
 obtain ⟨t,controlRun,tp,fields,_,_,fr⟩:=C.read_dispatch_execution work T tapeEnd B n (E.record q w pairs) x s
  pc workHeader ptr one metadata live bank (E.record_good q w pairs) bound
  (by simpa only [UniformNativeExchangeRecordMachine.record_length,Nat.add_assoc] using tableEnd) width code
 have fi:(⟨(E.record q w pairs).opcode,(E.record_good q w pairs).1⟩:Fin 7)=4:=Fin.ext (by rfl)
 have ep:t.pc=P.address .exchange:=exchange_pc t.pc (tp.trans (congrArg C.targets fi))
 have ba:t.natReg 3300=A:=(fr.natReg _ (by unfold C.ControlChanged;omega)).trans base
 have nk:t.natReg 5300=k:=(fr.natReg _ (by unfold C.ControlChanged;omega)).trans native
 obtain ⟨u,run,up,out,done,ef⟩:=UniformRecursiveNativeEntries.UniformNativeExchangeRecordMachine.entry q w k A T B n x
  pairs f t ep fields.cursor ba nk (printed_control fr bank) (present_control fr data) positive controlRun.final_bound
  (R.code_bound .exchange E.program.length B rfl code) (R.start_bound .loop B code) extent tableEnd width
 refine ⟨u,t,?_,up,out,done,fr,ef⟩
 convert controlRun.trans run using 1
 simp [UniformFixedNetworkOpcodeMachine.headCost,UniformNativeExchangeRecordMachine.record,C.dispatchCost]
 omega

/-- Actual opcode3 translates full k-bit arrays, retaining q,w and r as printed
geometry. It starts and ends at the same physical parent's loop. -/
theorem translation_loop {roles:ℕ}(q w rest k A E T recordBase work tapeEnd B n:ℕ)(x:Fin n→ℂ)
 (ds:List (Y.Direction roles w))(f:Fin roles→Fin (volume k)→Scalar)(s:State)
 (pc:s.pc=P.address .loop)(ptr:s.natReg 2850=recordBase)(base:s.natReg 3300=A)(native:s.natReg 5300=k)
 (restHeader:s.natReg 5301=rest)(shape:k=q*w+rest)(qp:1 ≤ q)(padded:2^(q*(w+rest)) ≤ B)
 (volumeHeader:s.natReg 4122=volume k)(fresh:E=work+4*volume k)(table:s.natReg 3389=T)
 (workHeader:s.natReg 4123=work)(one:s.natReg 4153=1)(metadata:s.natHeap (work-1)=some tapeEnd)(live:recordBase<tapeEnd)
 (bank:Printed recordBase (Y.record q w ds).data s)(data:Present A roles (volume k) f s)
 (bound:WordBound B s)(code:P.program.length ≤ B)(sourceBeforeTable:recordBase+(Y.record q w ds).data.length ≤ T)
 (separate:A+roles*volume k ≤ E)(tableEnd:T+2^q*2^q ≤ B)(extent:E+volume k ≤ B)(width:w+1 ≤ B):∃u t a,
 BoundedRuns P.program n x B s (Y.runtime q w rest k ds.length+51) u ∧ u.pc=P.address .loop ∧
 Present A roles (volume k) (Y.actions q w k ds f) u ∧ u.natReg 2850=recordBase+(Y.record q w ds).data.length ∧
 C.ControlFrame s t ∧ UniformRecursiveYRestore.Frame t a ∧ Y.FullFrame q A (roles*volume k) E T w k a u:=by
 have tb:T ≤ B:=by omega
 obtain ⟨t,controlRun,tp,fields,_,_,fr⟩:=C.read_dispatch_execution work recordBase tapeEnd B n (Y.record q w ds) x s
  pc workHeader ptr one metadata live bank (Y.record_good q w ds) bound (sourceBeforeTable.trans tb) width code
 have fi:(⟨(Y.record q w ds).opcode,(Y.record_good q w ds).1⟩:Fin 7)=3:=Fin.ext (by rfl)
 have ep:t.pc=P.address .yRestore:=translation_pc t.pc (tp.trans (congrArg C.targets fi))
 have keep(j:ℕ)(hj:¬C.ControlChanged j):t.natReg j=s.natReg j:=fr.natReg j hj
 have wt:t.natReg 4123=work:=(keep _ (by unfold C.ControlChanged;omega)).trans workHeader
 have vt:t.natReg 4122=volume k:=(keep _ (by unfold C.ControlChanged;omega)).trans volumeHeader
 have four:4 ≤ B:=by
  have pos:=Nat.two_pow_pos k
  unfold volume at fresh extent
  omega
 obtain ⟨a,restore,ap,buffer,af⟩:=UniformRecursiveYRestore.execution n B work (volume k) x t ep wt vt
  controlRun.final_bound (by omega) four code
 have ak(j:ℕ)(hj:¬C.ControlChanged j)(ha:¬UniformRecursiveYRestore.Changed j):a.natReg j=s.natReg j:=
  (af.natReg j ha).trans (keep j hj)
 have ba:a.natReg 3300=A:=(ak _ (by unfold C.ControlChanged;omega) (by unfold UniformRecursiveYRestore.Changed;omega)).trans base
 have nk:a.natReg 5300=k:=(ak _ (by unfold C.ControlChanged;omega) (by unfold UniformRecursiveYRestore.Changed;omega)).trans native
 have rh:a.natReg 5301=rest:=(ak _ (by unfold C.ControlChanged;omega) (by unfold UniformRecursiveYRestore.Changed;omega)).trans restHeader
 have xt:a.natReg 3389=T:=(ak _ (by unfold C.ControlChanged;omega) (by unfold UniformRecursiveYRestore.Changed;omega)).trans table
 have ac:a.natReg 2850=recordBase:=(af.natReg _ (by unfold UniformRecursiveYRestore.Changed;omega)).trans fields.cursor
 have eb:a.natReg 3364=E:=buffer.trans fresh.symm
 have bankA:Printed recordBase (Y.record q w ds).data a:=by
  intro j hj;rw[af.natHeap,fr.natHeap];exact bank j hj
 have dataA:Present A roles (volume k) f a:=by
  intro i j;rw[af.scalarHeap,fr.scalarHeap];exact data i j
 obtain ⟨u,run,up,out,done,yf⟩:=UniformRecursiveNativeEntries.UniformNativeYRecordMachine.entry q w rest k A E T recordBase B n x
  ds f a ap ac ba nk rh shape qp padded eb xt bankA dataA
  restore.final_bound (R.code_bound .translation Y.program.length B rfl code) (R.start_bound .loop B code)
  sourceBeforeTable separate tableEnd extent width
 refine ⟨u,t,a,?_,up,out,done,fr,af,yf⟩
 convert (controlRun.trans restore).trans run using 1
 simp [UniformFixedNetworkOpcodeMachine.headCost,UniformNativeYRecordMachine.record,C.dispatchCost]
 omega

/-- Marker opcodes2 and6 traverse their actual variable records. Full heaps
and roots are retained; fields and control scratch are the only changes. -/
theorem marker_loop (T work tapeEnd B n:ℕ)(r:Record)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=P.address .loop)(ptr:s.natReg 2850=T)(workHeader:s.natReg 4123=work)(one:s.natReg 4153=1)
 (metadata:s.natHeap (work-1)=some tapeEnd)(live:T<tapeEnd)(bank:Printed T r.data s)
 (marker:r.opcode=2∨r.opcode=6)(good:UniformFixedNetworkOpcodeMachine.WellFormed r)(bound:WordBound B s)
 (code:P.program.length ≤ B)(extent:T+r.data.length ≤ B)(width:r.width+1 ≤ B):∃u t,
 BoundedRuns P.program n x B s (6+2*UniformFixedNetworkOpcodeMachine.headCost r+C.dispatchCost r.opcode) u ∧
 u.pc=P.address .loop ∧ u.natReg 2850=T+r.data.length ∧ C.ControlFrame s t ∧ UniformFixedNetworkOpcodeMachine.Frame t u:=by
 obtain ⟨t,controlRun,tp,fields,_,_,fr⟩:=C.read_dispatch_execution work T tapeEnd B n r x s
  pc workHeader ptr one metadata live bank good bound extent width code
 have ep:t.pc=P.address .marker:=by
  rcases marker with m2|m6
  · have fi:(⟨r.opcode,good.1⟩:Fin 7)=2:=Fin.ext m2
    exact marker2_pc t.pc (tp.trans (congrArg C.targets fi))
  · have fi:(⟨r.opcode,good.1⟩:Fin 7)=6:=Fin.ext m6
    exact marker6_pc t.pc (tp.trans (congrArg C.targets fi))
 obtain ⟨u,run,up,done,mf⟩:=UniformRecursiveNativeEntries.UniformFixedNetworkMarkerMachine.entry T B n r x t ep fields.cursor
  controlRun.final_bound (printed_control fr bank) marker good extent width
  (R.code_bound .marker UniformFixedNetworkMarkerMachine.program.length B rfl code) (R.start_bound .loop B code)
 refine ⟨u,t,?_,up,done,fr,mf⟩
 convert controlRun.trans run using 1
 omega

end
end ExactFourierCircuits.UniformRecursiveNativeRecords

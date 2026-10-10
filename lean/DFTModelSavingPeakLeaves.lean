import DFTModelSavingPeakPaired
import DFTModelSavingNativeY
import DFTModelSavingScalarBounds
import DFTModelSavingCostDispatch

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingPeak
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelClockControl
open DFTModelSavingResidualBoolean UniformFixedNetworkScheduleMachine
noncomputable section
attribute [local irreducible] DFTModelSavingRecords.dispatch DFTModelSavingScalar.program
  DFTModelRecursiveExchange.program DFTModelSavingY.program

/-- An arbitrary Boolean bank admits a paired representation for peak proofs;
this is not an assertion about source executions or canonical role flags. -/
theorem y_peak {R m : ℕ} (q r k B : ℕ) (I : ℂ) (raw : Tape ℕ)
    (ds : List (UniformNativeYRecordMachine.Direction R m))
    (source : DFTModelSavingY.RecordSource q ds raw) (v : Tape Tagged.T)
    (len : v.len=R*2^k) (before : Boolean v)
    (positive : 0 < R) (shape : k=q*m+r) (qp : 1 ≤ q)
    (extent : R*2^k ≤ B) (recordEnd : 8+(m+1)*ds.length ≤ B)
    (padded : 2^(q*(m+r)) ≤ B) (square : 2^q*2^q ≤ B) :
    (run (DFTModelSavingY.program R) (r,(raw,((k,I),v)))).peak ≤ 4*B+2 := by
  obtain ⟨f,f0,eq⟩:=exists_paired v len before
  rw [eq]
  exact DFTModelSavingY.program_peak q r k B I raw ds source f f0 positive shape qp extent recordEnd padded square

theorem exchange_peak {R : ℕ} (q w k B : ℕ)
    (ps : List (UniformNativeExchangeRecordMachine.Pair R)) (I : ℂ)
    (v : Tape Tagged.T) (len : v.len=R*2^k) (before : Boolean v)
    (roles : 0 < R) (endFit : 8+4*ps.length ≤ B) (fit : R*2^k ≤ B) :
    (run (DFTModelRecursiveExchange.program R)
      (DFTModelCacheRecords.dataTape (UniformNativeExchangeRecordMachine.record q w ps).data,
        ((k,I),v))).peak ≤ B := by
  obtain ⟨f,f0,eq⟩:=exists_paired v len before
  rw [eq,DFTModelSavingNativeExchange.recordTape_eq]
  exact DFTModelRecursiveExchange.program_peak_bound q w ps (by positivity) roles f f0 k B I endFit fit

theorem exchange_decode_source {R : ℕ} (q w : ℕ)
    (ps : List (UniformNativeExchangeRecordMachine.Pair R)) (raw : Tape ℕ)
    (source : DFTModelSavingDirection.RawSource (UniformNativeExchangeRecordMachine.record q w ps) raw) :
    (run DFTModelRecursiveExchange.decode raw).val=DFTModelRecursiveExchange.pairTape ps := by
  have count : raw.look 6 0=ps.length := source.header ⟨6,by decide⟩
  rw [DFTModelRecursiveExchange.decode_value,count]
  apply DFTModelSavingY.tape_ext
    (a:=Tape.tab ps.length (fun i=>(raw.look (4*i+8) 0,raw.look (4*i+9) 0)))
    (b:=DFTModelRecursiveExchange.pairTape ps) DFTModelRecursiveExchange.PairNat.blank rfl
  intro j
  by_cases hj : j<ps.length
  · rw [Tape.look_of_lt _ _ hj,DFTModelRecursiveExchange.pairTape_lookup ps j hj]
    have h1 : 4*j+8<(UniformNativeExchangeRecordMachine.record q w ps).data.length := by
      rw [UniformNativeExchangeRecordMachine.record_length];omega
    have h2 : 4*j+9<(UniformNativeExchangeRecordMachine.record q w ps).data.length := by
      rw [UniformNativeExchangeRecordMachine.record_length];omega
    have p:=DFTModelRecursiveExchange.recordTape_pair q w ps j hj
    rw [Tape.look_of_lt _ _ h1,Tape.look_of_lt _ _ h2] at p
    exact (Prod.ext (source _ h1) (source _ h2)).trans p
  · rw [Tape.look_of_le _ _ (by change ps.length ≤ j;omega),Tape.look_of_le _ _ (by change ps.length ≤ j;omega)]

theorem exchange_peak_raw {R : ℕ} (q w k B : ℕ)
    (ps : List (UniformNativeExchangeRecordMachine.Pair R)) (I : ℂ) (raw : Tape ℕ)
    (source : DFTModelSavingDirection.RawSource (UniformNativeExchangeRecordMachine.record q w ps) raw)
    (v : Tape Tagged.T) (len : v.len=R*2^k) (before : Boolean v)
    (roles : 0<R) (endFit : 8+4*ps.length ≤ B) (fit : R*2^k ≤ B) :
    (run (DFTModelRecursiveExchange.program R) (raw,((k,I),v))).peak ≤ B := by
  obtain ⟨f,f0,eq⟩:=exists_paired v len before
  rw [eq,DFTModelRecursiveExchange.program_run]
  change max (max (run DFTModelRecursiveExchange.decode raw).peak
    (run (DFTModelRecursiveExchange.pairsProgram R)
      ((run DFTModelRecursiveExchange.decode raw).val,((k,I),DFTModelRecursiveScalarSource.paired f f0))).peak) 0 ≤ B
  rw [exchange_decode_source q w ps raw source,max_zero]
  refine max_le (DFTModelRecursiveExchange.decode_peak raw B ?_)
    (DFTModelRecursiveExchange.pairs_peak_bound ps (by positivity) roles f f0 k B I (by omega) fit)
  have count : raw.look 6 0=ps.length := source.header ⟨6,by decide⟩
  rwa [count]

lemma field_ifz_peak {t : Ty} (j r : ℕ) (raw : Tape ℕ) (node : Node.T)
    (f g : Code false ChildPort DFTModelSavingRecords.Input t) (h : Handler ChildPort) :
    (Code.run (.ifz (.importClosed (DFTModelSavingRecords.field j)) f g) h (r,(raw,node))).peak=
      max j (if raw.look j 0=0 then (Code.run f h (r,(raw,node))).peak else (Code.run g h (r,(raw,node))).peak) := by
  change ((((run (DFTModelSavingRecords.field j) (r,(raw,node))).pay 1 0).pass
    (fun a=>if a=0 then Code.run f h (r,(raw,node)) else Code.run g h (r,(raw,node)))).pay 1 0).peak=_
  rw [DFTModelSavingCost.record_field_run]
  by_cases hc:raw.look j 0=0 <;> simp [Bill.pass,Bill.pay,hc]

lemma opcodeTest_run (j r : ℕ) (raw : Tape ℕ) (node : Node.T) :
    run (DFTModelSavingRecords.opcodeTest j) (r,(raw,node))=
      ⟨raw.look 0 0-j,11,max j (raw.look 0 0-j),True⟩ := by
  simp only [DFTModelSavingRecords.opcodeTest,DFTModelResidualCore.binary,run,Code.run,
    DFTModelSavingRecords.field,DFTModelSavingRecords.raw,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]
  simp only [true_and]
  congr 1
  omega

lemma opcode_ifz_peak {t : Ty} (j r : ℕ) (raw : Tape ℕ) (node : Node.T)
    (f g : Code false ChildPort DFTModelSavingRecords.Input t) (h : Handler ChildPort) :
    (Code.run (.ifz (.importClosed (DFTModelSavingRecords.opcodeTest j)) f g) h (r,(raw,node))).peak=
      max (max j (raw.look 0 0-j))
        (if raw.look 0 0-j=0 then (Code.run f h (r,(raw,node))).peak else (Code.run g h (r,(raw,node))).peak) := by
  change ((((run (DFTModelSavingRecords.opcodeTest j) (r,(raw,node))).pay 1 0).pass
    (fun a=>if a=0 then Code.run f h (r,(raw,node)) else Code.run g h (r,(raw,node)))).pay 1 0).peak=_
  rw [opcodeTest_run]
  by_cases hc:raw.look 0 0-j=0 <;> simp [Bill.pass,Bill.pay,hc]

lemma import_peak {s t : Ty} (f : Prog false s t) (h : Handler ChildPort) (x : s.T) :
    (Code.run (.importClosed f) h x).peak=(run f x).peak := by
  change max (run f x).peak 0=_
  exact max_zero _

lemma comp_peak {s t u : Ty} (f : Code false ChildPort s t) (g : Code false ChildPort t u)
    (h : Handler ChildPort) (x : s.T) :
    (Code.run (.comp f g) h x).peak=max (Code.run f h x).peak
      (Code.run g h (Code.run f h x).val).peak := by
  change max (max _ _) 0=_
  exact max_zero _

/-- Exact maximum of the actual selected opcode branch and finite tests. -/
theorem dispatch_peak (R rest : ℕ) (raw : Tape ℕ) (node : Node.T)
    (h : Handler DFTModelSavingRecords.Port) :
    (Code.run (DFTModelSavingRecords.dispatch R) h (rest,(raw,node))).peak=
      if raw.look 0 0=0 then (Code.run DFTModelSavingRecords.residual h (rest,(raw,node))).peak
      else if raw.look 0 0-1=0 then max (run (DFTModelSavingScalar.program R) (raw,node)).peak 1
      else if raw.look 0 0-2=0 then 2
      else if raw.look 0 0-3=0 then max (run (DFTModelSavingY.program R) (rest,(raw,node))).peak 3
      else if raw.look 0 0-4=0 then max (run (DFTModelRecursiveExchange.program R) (raw,node)).peak 4
      else if raw.look 0 0-5=0 then max (Code.run DFTModelSavingRecords.padding h (rest,(raw,node))).peak 5
      else max 5 (raw.look 0 0-1) := by
  rw [DFTModelSavingRecords.dispatch,field_ifz_peak]
  rw [opcode_ifz_peak,opcode_ifz_peak,opcode_ifz_peak,opcode_ifz_peak,opcode_ifz_peak]
  simp only [comp_peak,import_peak,DFTModelSavingCost.code_import_value]
  rw [DFTModelSavingCost.scalarArgs_run,DFTModelSavingCost.exchangeArgs_run,
    DFTModelSavingCost.initial_run]
  dsimp only [Bill.val,Bill.peak]
  split_ifs <;> omega
lemma marker_six_peak (R rest : ℕ) (raw : Tape ℕ) (node : Node.T)
    (h : Handler ChildPort) (op : raw.look 0 0=6) :
    (Code.run (DFTModelSavingRecords.dispatch R) h (rest,(raw,node))).peak=5 := by
  rw [dispatch_peak,op]
  norm_num
lemma marker_two_peak (R rest : ℕ) (raw : Tape ℕ) (node : Node.T)
    (h : Handler ChildPort) (op : raw.look 0 0=2) :
    (Code.run (DFTModelSavingRecords.dispatch R) h (rest,(raw,node))).peak=2 := by
  rw [dispatch_peak,op]
  norm_num

lemma scalar_dispatch_peak (R rest : ℕ) (raw : Tape ℕ) (node : Node.T)
    (h : Handler ChildPort) (op : raw.look 0 0=1) :
    (Code.run (DFTModelSavingRecords.dispatch R) h (rest,(raw,node))).peak=
      max (run (DFTModelSavingScalar.program R) (raw,node)).peak 1 := by
  rw [dispatch_peak,op]
  norm_num only [Nat.one_ne_zero,Nat.sub_self,ite_false,ite_true]

lemma y_dispatch_peak (R rest : ℕ) (raw : Tape ℕ) (node : Node.T)
    (h : Handler ChildPort) (op : raw.look 0 0=3) :
    (Code.run (DFTModelSavingRecords.dispatch R) h (rest,(raw,node))).peak=
      max (run (DFTModelSavingY.program R) (rest,(raw,node))).peak 3 := by
  rw [dispatch_peak,op]
  norm_num only [Nat.reduceEqDiff,Nat.reduceSub,ite_false,ite_true]

lemma exchange_dispatch_peak (R rest : ℕ) (raw : Tape ℕ) (node : Node.T)
    (h : Handler ChildPort) (op : raw.look 0 0=4) :
    (Code.run (DFTModelSavingRecords.dispatch R) h (rest,(raw,node))).peak=
      max (run (DFTModelRecursiveExchange.program R) (raw,node)).peak 4 := by
  rw [dispatch_peak,op]
  norm_num only [Nat.reduceEqDiff,Nat.reduceSub,ite_false,ite_true]

lemma padding_dispatch_peak (R rest : ℕ) (raw : Tape ℕ) (node : Node.T)
    (h : Handler ChildPort) (op : raw.look 0 0=5) :
    (Code.run (DFTModelSavingRecords.dispatch R) h (rest,(raw,node))).peak=
      max (Code.run DFTModelSavingRecords.padding h (rest,(raw,node))).peak 5 := by
  rw [dispatch_peak,op]
  norm_num only [Nat.reduceEqDiff,Nat.reduceSub,ite_false,ite_true]

end
end ExactFourierCircuits.DFTModelSavingPeak

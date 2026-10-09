import DFTModelRecursiveExchangeLoop

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelRecursiveExchange
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelRecursiveScalarCore
noncomputable section

abbrev Raw := Ty.a w
abbrev RawCell := p Raw w
abbrev Input := p Raw DFTModelClockControl.Node

def readCount : Prog false Raw w := .comp (.fork (.atom .id) (.atom (.lit 6))) (.atom .look)
def field (b : ℕ) : Prog false RawCell w :=
  .comp (.fork (.atom .fst)
    (nat .add (nat .mul (.atom .snd) (.atom (.lit 4))) (.atom (.lit b)))) (.atom .look)
def decodeCell : Prog false RawCell PairNat := .fork (field 8) (field 9)
def decode : Prog false Raw PairTape := .tab readCount decodeCell

def program (R : ℕ) : Prog false Input DFTModelClockControl.Node :=
  .comp (.fork (.comp (.atom .fst) decode) (.atom .snd)) (pairsProgram R)

attribute [local irreducible] pairProgram body pairsProgram program

def recordTape {R : ℕ} (q w : ℕ) (ps : List (UniformNativeExchangeRecordMachine.Pair R)) : Tape ℕ :=
  let xs := (UniformNativeExchangeRecordMachine.record q w ps).data
  ⟨xs.length,fun i => xs[i]⟩

theorem readCount_run (raw : Tape ℕ) :
    run readCount raw=⟨raw.look 6 0,5,6,True⟩ := by
  simp [readCount,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]

theorem field_run (b i : ℕ) (raw : Tape ℕ) :
    run (field b) (raw,i)=⟨raw.look (4*i+b) 0,13,max 4 (max b (4*i+b)),True⟩ := by
  simp only [field,nat,comp_run,fork_run,atom_run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,and_true,max_zero,zero_max,Ty.blank]
  congr 1
  · rw [Nat.mul_comm i 4]
  · omega

theorem decodeCell_run (i : ℕ) (raw : Tape ℕ) :
    run decodeCell (raw,i)=
      ⟨(raw.look (4*i+8) 0,raw.look (4*i+9) 0),27,4*i+9,True⟩ := by
  rw [decodeCell,fork_run,field_run,field_run]
  simp only [Bill.pass,Bill.one,true_and]
  congr 1
  omega

theorem decode_value (raw : Tape ℕ) :
    (run decode raw).val=Tape.tab (raw.look 6 0)
      (fun i => (raw.look (4*i+8) 0,raw.look (4*i+9) 0)) := by
  rw [decode,DFTModelRecursiveScalar.tab_run,readCount_run]
  change (Bill.tab (raw.look 6 0) PairNat.blank (fun i => run decodeCell (raw,i))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab (raw.look 6 0)) (funext (fun i => congrArg Bill.val (decodeCell_run i raw)))

theorem decode_valid (raw : Tape ℕ) : (run decode raw).valid := by
  rw [decode,DFTModelRecursiveScalar.tab_run,readCount_run]
  change True ∧ (Bill.tab (raw.look 6 0) PairNat.blank (fun i => run decodeCell (raw,i))).valid
  refine ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 ?_⟩
  intro i _
  rw [decodeCell_run]
  trivial

theorem decode_work (raw : Tape ℕ) : (run decode raw).work=8+31*(raw.look 6 0) := by
  rw [decode,DFTModelRecursiveScalar.tab_run,readCount_run]
  change 5+(Bill.tab (raw.look 6 0) PairNat.blank (fun i => run decodeCell (raw,i))).work+1=_
  rw [ModelEquivalenceInterpreter.tab_work]
  have h : (∑i ∈ Finset.range (raw.look 6 0),(run decodeCell (raw,i)).work)=27*(raw.look 6 0) := by
    calc
      _ = ∑i ∈ Finset.range (raw.look 6 0),27 := Finset.sum_congr rfl (fun i _ => congrArg Bill.work (decodeCell_run i raw))
      _ = _ := by simp [Nat.mul_comm]
  rw [h]
  ring

theorem decode_peak (raw : Tape ℕ) (B : ℕ) (endFit : 8+4*(raw.look 6 0)≤B) :
    (run decode raw).peak≤B := by
  rw [decode,DFTModelRecursiveScalar.tab_run,readCount_run]
  change max (max 6 (Bill.tab (raw.look 6 0) PairNat.blank
    (fun i => run decodeCell (raw,i))).peak) 0≤B
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp only [max_zero]
  refine max_le (by omega) (max_le (by omega) ?_)
  apply Finset.sup_le
  intro i hi
  have ilt : i<raw.look 6 0 := Finset.mem_range.mp hi
  rw [decodeCell_run]
  change 4*i+9≤B
  omega

theorem body_first {R : ℕ} (ps : List (UniformNativeExchangeRecordMachine.Pair R))
    (i : ℕ) (hi : i<ps.length) :
    ((UniformNativeExchangeRecordMachine.body ps)[4*i]?).getD 0=(ps[i]).first.val := by
  induction ps generalizing i with
  | nil => simp at hi
  | cons p ps ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have h : i<ps.length := by simpa using hi
      rw [show 4*(i+1)=4*i+4 by omega]
      change ((UniformNativeExchangeRecordMachine.body ps)[4*i]?).getD 0=(ps[i]).first.val
      exact ih i h

theorem body_second {R : ℕ} (ps : List (UniformNativeExchangeRecordMachine.Pair R))
    (i : ℕ) (hi : i<ps.length) :
    ((UniformNativeExchangeRecordMachine.body ps)[4*i+1]?).getD 0=(ps[i]).second.val := by
  induction ps generalizing i with
  | nil => simp at hi
  | cons p ps ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have h : i<ps.length := by simpa using hi
      rw [show 4*(i+1)+1=(4*i+1)+4 by omega]
      change ((UniformNativeExchangeRecordMachine.body ps)[4*i+1]?).getD 0=(ps[i]).second.val
      exact ih i h

theorem recordTape_count {R : ℕ} (q w : ℕ) (ps : List (UniformNativeExchangeRecordMachine.Pair R)) :
    (recordTape q w ps).look 6 0=ps.length := by
  rw [Tape.look_of_lt _ _ (show 6<(recordTape q w ps).len by
    change 6<(UniformNativeExchangeRecordMachine.record q w ps).data.length
    rw [UniformNativeExchangeRecordMachine.record_length];omega)]
  rfl

theorem recordTape_pair {R : ℕ} (q w : ℕ) (ps : List (UniformNativeExchangeRecordMachine.Pair R))
    (i : ℕ) (hi : i<ps.length) :
    ((recordTape q w ps).look (4*i+8) 0,(recordTape q w ps).look (4*i+9) 0)=
      ((ps[i]).first.val,(ps[i]).second.val) := by
  have hlen : (recordTape q w ps).len=8+4*ps.length :=
    UniformNativeExchangeRecordMachine.record_length q w ps
  rw [Tape.look_of_lt _ _ (show 4*i+8<(recordTape q w ps).len by omega),
    Tape.look_of_lt _ _ (show 4*i+9<(recordTape q w ps).len by omega)]
  refine Prod.ext ?_ ?_
  · have hb : 4*i<(UniformNativeExchangeRecordMachine.body ps).length := by
      rw [UniformNativeExchangeRecordMachine.body_length];omega
    change ((UniformNativeExchangeRecordMachine.body ps)[4*i]'hb)=_
    have h := body_first ps i hi
    simpa only [List.getElem?_eq_getElem (show 4*i<(UniformNativeExchangeRecordMachine.body ps).length by
      rw [UniformNativeExchangeRecordMachine.body_length];omega),Option.getD_some] using h
  · have hb : 4*i+1<(UniformNativeExchangeRecordMachine.body ps).length := by
      rw [UniformNativeExchangeRecordMachine.body_length];omega
    change ((UniformNativeExchangeRecordMachine.body ps)[4*i+1]'hb)=_
    have h := body_second ps i hi
    simpa only [List.getElem?_eq_getElem (show 4*i+1<(UniformNativeExchangeRecordMachine.body ps).length by
      rw [UniformNativeExchangeRecordMachine.body_length];omega),Option.getD_some] using h

theorem decode_record {R : ℕ} (q w : ℕ) (ps : List (UniformNativeExchangeRecordMachine.Pair R)) :
    (run decode (recordTape q w ps)).val=pairTape ps := by
  rw [decode_value,recordTape_count]
  refine tape_ext PairNat.blank rfl ?_
  intro i
  by_cases hi : i<ps.length
  · rw [Tape.look_of_lt _ _ hi,pairTape_lookup ps i hi]
    exact recordTape_pair q w ps i hi
  · have hl : ps.length ≤ i := by omega
    rw [Tape.look_of_le _ _ hl,Tape.look_of_le _ _ hl]

end
end ExactFourierCircuits.DFTModelRecursiveExchange

import DFTModelBinaryPhysical

set_option autoImplicit false

/-! One fresh scalar tape restores physical order after the pairwise C stage.
The input pair tape is readonly; each output reads just its owning pair. -/
namespace ExactFourierCircuits.DFTModelBinaryUnpacking
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Input := p w (p w (Ty.a DFTModelBinaryAffinePair.Pair))
abbrev CellInput := p Input w

def length : Prog false Input w :=
  .comp (.fork (.atom .fst) (.atom (.lit 2))) (.atom (.int .mul))
def stride : Prog false CellInput w :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def oldTape : Prog false CellInput (Ty.a DFTModelBinaryAffinePair.Pair) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))
def quotient : Prog false CellInput w :=
  .comp (.fork (.atom .snd) stride) (.atom (.int .div))
def half : Prog false CellInput w :=
  .comp (.fork quotient (.atom (.lit 2))) (.atom (.int .div))
def base : Prog false CellInput w :=
  .comp (.fork half stride) (.atom (.int .mul))
def remainder : Prog false CellInput w :=
  .comp (.fork (.atom .snd) stride) (.atom (.int .mod))
def index : Prog false CellInput w :=
  .comp (.fork base remainder) (.atom (.int .add))
def role : Prog false CellInput w :=
  .comp (.fork quotient (.atom (.lit 2))) (.atom (.int .mod))
def oldPair : Prog false CellInput DFTModelBinaryAffinePair.Pair :=
  .comp (.fork oldTape index) (.atom .look)
def select : Prog false (p DFTModelBinaryAffinePair.Pair w) DFTModelAffine.Tagged :=
  .ifz (.atom .snd) (.comp (.atom .fst) (.atom .fst))
    (.comp (.atom .fst) (.atom .snd))
def cell : Prog false CellInput DFTModelAffine.Tagged :=
  .comp (.fork oldPair role) select
def program : Prog false Input (Ty.a DFTModelAffine.Tagged) := .tab length cell

def indexValue (P k : ℕ) : ℕ := (k/P/2)*P+k%P
def indexPeak (P k : ℕ) : ℕ :=
  max (max (max (max (max (k/P) 2) (k/P/2)) ((k/P/2)*P)) (k%P)) (indexValue P k)
def rolePeak (P k : ℕ) : ℕ := max (max (k/P) 2) (k/P%2)
def cellValue (P : ℕ) (v : Tape DFTModelBinaryAffinePair.Pair.T) (k : ℕ) :
    DFTModelAffine.Tagged.T :=
  if k/P%2=0 then (v.look (indexValue P k) ((0,(0,0)),(0,(0,0)))).1
    else (v.look (indexValue P k) ((0,(0,0)),(0,(0,0)))).2

theorem cell_run (M P : ℕ) (v : Tape DFTModelBinaryAffinePair.Pair.T) (k : ℕ) :
    run cell ((M,(P,v)),k) =
      ⟨cellValue P v k,61,max (indexPeak P k) (rolePeak P k),True⟩ := by
  by_cases h : k/P%2=0 <;>
    simp [cell,oldPair,role,index,base,half,remainder,quotient,stride,oldTape,select,
      cellValue,indexValue,indexPeak,rolePeak,run,Code.run,Atom.run,NOp.run,
      Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank,h,max_left_comm,max_comm]

theorem length_run (M P : ℕ) (v : Tape DFTModelBinaryAffinePair.Pair.T) :
    run length (M,(P,v)) = ⟨M*2,5,max 2 (M*2),True⟩ := by
  simp [length,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem integer_bounds (P k B : ℕ) (hk : k≤B) (two : 2≤B) :
    indexPeak P k≤B ∧ rolePeak P k≤B := by
  have hq : k/P≤k := Nat.div_le_self k P
  have hh : k/P/2≤k/P := Nat.div_le_self (k/P) 2
  have hm : (k/P/2)*P≤k := (Nat.mul_le_mul_right P hh).trans (Nat.div_mul_le_self k P)
  have hi : indexValue P k≤k := by
    have h := Nat.mul_le_mul_right P hh
    have eq := Nat.mod_add_div k P
    unfold indexValue
    nlinarith
  have hr : k%P≤k := Nat.mod_le k P
  have ht : k/P%2<2 := Nat.mod_lt _ (by decide)
  simp only [indexPeak,rolePeak,max_le_iff]
  omega

theorem program_value (M P : ℕ) (v : Tape DFTModelBinaryAffinePair.Pair.T) :
    (run program (M,(P,v))).val = Tape.tab (M*2) (cellValue P v) := by
  change (((run length (M,(P,v))).pass (fun l =>
    Bill.tab l DFTModelAffine.Tagged.blank (fun k => run cell ((M,(P,v)),k)))).pay 1 0).val = _
  rw [length_run]
  change (Bill.tab (M*2) DFTModelAffine.Tagged.blank
    (fun k => run cell ((M,(P,v)),k))).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab (M*2)) (funext (fun k => congrArg Bill.val (cell_run M P v k)))

theorem program_work (M P : ℕ) (v : Tape DFTModelBinaryAffinePair.Pair.T) :
    (run program (M,(P,v))).work = 130*M+8 := by
  change (((run length (M,(P,v))).pass (fun l =>
    Bill.tab l DFTModelAffine.Tagged.blank (fun k => run cell ((M,(P,v)),k)))).pay 1 0).work = _
  rw [length_run]
  change 5+(Bill.tab (M*2) DFTModelAffine.Tagged.blank
    (fun k => run cell ((M,(P,v)),k))).work+1 = _
  rw [ModelEquivalenceInterpreter.tab_work]
  have h : (fun k => (run cell ((M,(P,v)),k)).work) = (fun _ => 61) := by
    funext k
    exact congrArg Bill.work (cell_run M P v k)
  rw [h]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem program_valid (M P : ℕ) (v : Tape DFTModelBinaryAffinePair.Pair.T) :
    (run program (M,(P,v))).valid := by
  change (((run length (M,(P,v))).pass (fun l =>
    Bill.tab l DFTModelAffine.Tagged.blank (fun k => run cell ((M,(P,v)),k)))).pay 1 0).valid
  rw [length_run]
  refine ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 ?_⟩
  intro k _
  rw [cell_run]
  trivial

theorem program_peak (M P B : ℕ) (v : Tape DFTModelBinaryAffinePair.Pair.T)
    (extent : M*2≤B) (two : 2≤B) : (run program (M,(P,v))).peak≤B := by
  change (((run length (M,(P,v))).pass (fun l =>
    Bill.tab l DFTModelAffine.Tagged.blank (fun k => run cell ((M,(P,v)),k)))).pay 1 0).peak≤B
  rw [length_run]
  simp only [Bill.pass,Bill.pay,max_zero]
  apply max_le (max_le two extent)
  rw [ModelEquivalenceInterpreter.tab_peak]
  apply max_le extent
  apply Finset.sup_le
  intro k hk
  rw [cell_run]
  have h := integer_bounds P k B ((Nat.le_of_lt (Finset.mem_range.mp hk)).trans extent) two
  exact max_le h.1 h.2

/-- The arithmetic decoder is precisely the inverse of the source's explicit
finite address permutation. No inverse table is assumed. -/
theorem inverse_values (P Q : ℕ) (k : Fin (P*2*Q)) :
    ((UniformTensorAddressMachine.fiberEquiv P 2 Q).symm k).1.val=indexValue P k.val ∧
    ((UniformTensorAddressMachine.fiberEquiv P 2 Q).symm k).2.val=k.val/P%2 := by
  constructor
  · change k.val%P+P*(k.val/P/2)=indexValue P k.val
    unfold indexValue
    ring
  · rfl

theorem inverse_lookup (P Q : ℕ) (v : Tape DFTModelBinaryAffinePair.Pair.T)
    (k : Fin (P*2*Q)) :
    (run program (P*Q,(P,v))).val.look k.val (0,(0,0)) =
      let jt := (UniformTensorAddressMachine.fiberEquiv P 2 Q).symm k
      if jt.2=0 then (v.look jt.1.val ((0,(0,0)),(0,(0,0)))).1
        else (v.look jt.1.val ((0,(0,0)),(0,(0,0)))).2 := by
  rw [program_value]
  have lt : k.val<P*Q*2 := by convert k.isLt using 1; ring
  simp only [Tape.look,Tape.tab,lt,↓reduceDIte]
  obtain ⟨hi,ht⟩ := inverse_values P Q k
  rw [hi]
  have eq : ((UniformTensorAddressMachine.fiberEquiv P 2 Q).symm k).2=0 ↔ k.val/P%2=0 := by
    rw [← ht]
    simp
  simp only [cellValue,eq,Tape.look]

end
end ExactFourierCircuits.DFTModelBinaryUnpacking

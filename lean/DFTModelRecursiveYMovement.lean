import DFTModelResidualPeakBlock
import DFTModelAffinePaired

set_option autoImplicit false

/-! One fresh readonly gather of a complete role-major bank. Each element
contains both affine channels. Only the chosen role is XOR translated; the
XOR table and its digit width are ordinary prepared metadata. -/
namespace ExactFourierCircuits.DFTModelRecursiveYMovement
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
noncomputable section

abbrev Input (t : Ty) := p (p w w) (p (p w w) (p (Ty.a w) (p w (Ty.a t))))
abbrev CellInput (t : Ty) := p (Input t) w
def volume (t : Ty) : Prog false (CellInput t) w :=
  .comp (.atom .fst) (.comp (.atom .fst) (.atom .fst))
def blocks (t : Ty) : Prog false (CellInput t) w :=
  .comp (.atom .fst) (.comp (.atom .fst) (.atom .snd))
def radix (t : Ty) : Prog false (CellInput t) w :=
  .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .fst) (.atom .fst)))
def role (t : Ty) : Prog false (CellInput t) w :=
  .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .fst) (.atom .snd)))
def table (t : Ty) : Prog false (CellInput t) (Ty.a w) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def mask (t : Ty) : Prog false (CellInput t) w :=
  .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd)
    (.comp (.atom .snd) (.atom .fst))))
def bank (t : Ty) : Prog false (CellInput t) (Ty.a t) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd)
    (.comp (.atom .snd) (.atom .snd))))
def quotient (t : Ty) : Prog false (CellInput t) w :=
  binary .div (.atom .snd) (volume t)
def remainder (t : Ty) : Prog false (CellInput t) w :=
  binary .mod (.atom .snd) (volume t)
def difference (t : Ty) : Prog false (CellInput t) w := binary .add
  (binary .sub (quotient t) (role t)) (binary .sub (role t) (quotient t))
def selectedMask (t : Ty) : Prog false (CellInput t) w :=
  .ifz (difference t) (mask t) (.atom (.lit 0))
def argument (t : Ty) : Prog false (CellInput t) DFTModelResidualBlockXor.Input :=
  .fork (blocks t) (.fork (radix t) (.fork (table t)
    (.fork (remainder t) (selectedMask t))))
def shifted (t : Ty) : Prog false (CellInput t) w :=
  .comp (argument t) DFTModelResidualBlockXor.program
def address (t : Ty) : Prog false (CellInput t) w :=
  binary .add (binary .mul (quotient t) (volume t)) (shifted t)
def cell (t : Ty) : Prog false (CellInput t) t :=
  .comp (.fork (bank t) (address t)) (.atom .look)
def length (t : Ty) : Prog false (Input t) w :=
  .comp (.comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))) (.atom .len)
def program (t : Ty) : Prog false (Input t) (Ty.a t) := .tab (length t) (cell t)

def input (t : Ty) (q m V r a : ℕ) (v : Tape t.T) : (Input t).T :=
  ((V,m),((2^q,r),((run DFTModelResidualTable.program q).val,(a,v))))
def chosen (V r a j : ℕ) := if j/V=r then a else 0
def index (V r a j : ℕ) := j/V*V+(j%V^^^chosen V r a j)
def data (t : Ty) (V r a : ℕ) (v : Tape t.T) :=
  Tape.tab v.len (fun j=>v.look (index V r a j) t.blank)

theorem argument_value (t : Ty) (q m V r a j : ℕ) (v : Tape t.T) :
    (run (argument t) (input t q m V r a v,j)).val=
      DFTModelResidualBlockXor.input q m (j%V) (chosen V r a j) := by
  have h : (j/V-r=0 ∧ r-j/V=0) ↔ j/V=r := by omega
  by_cases eq : j / V = r <;>
    simp [argument,blocks,radix,table,remainder,selectedMask,difference,quotient,
      role,volume,mask,binary,input,chosen,DFTModelResidualBlockXor.input,
      run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,h,eq]

theorem cell_value (t : Ty) (q m V r a j : ℕ) (v : Tape t.T)
    (pos : 0 < V) (size : V ≤ 2^(q*m)) (small : a < 2^(q*m)) :
    (run (cell t) (input t q m V r a v,j)).val=v.look (index V r a j) t.blank := by
  have low : j%V<2^(q*m) := (Nat.mod_lt j pos).trans_le size
  have chosenSmall : chosen V r a j<2^(q*m) := by
    unfold chosen;split_ifs
    · exact small
    · exact Nat.two_pow_pos _
  have shiftedValue : (run (shifted t) (input t q m V r a v,j)).val=j%V^^^chosen V r a j := by
    change (run DFTModelResidualBlockXor.program
      (run (argument t) (input t q m V r a v,j)).val).val=_
    rw [argument_value]
    exact DFTModelResidualBlockXor.program_value q m _ _ low chosenSmall
  simpa only [cell,address,bank,quotient,volume,binary,input,index,
    run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
    using congrArg (fun u=>v.look (j/V*V+u) t.blank) shiftedValue

theorem argument_work (t : Ty) (q m V r a j : ℕ) (v : Tape t.T) :
    (run (argument t) (input t q m V r a v,j)).work ≤ 89 := by
  by_cases eq : j/V-r=0 ∧ r-j/V=0 <;>
    simp [argument,blocks,radix,table,remainder,selectedMask,difference,quotient,
      role,volume,mask,binary,input,run,Code.run,Atom.run,NOp.run,
      Bill.pass,Bill.pay,Bill.one,Bill.word,eq]

theorem cell_work (t : Ty) (q m V r a j : ℕ) (v : Tape t.T) :
    (run (cell t) (input t q m V r a v,j)).work ≤ 120*m+150 := by
  have aw:=argument_work t q m V r a j v
  have sv : (run (argument t) (input t q m V r a v,j)).val.1=m := by
    rw [argument_value];rfl
  have sw : (run (shifted t) (input t q m V r a v,j)).work≤120*m+106 := by
    change (run (argument t) (input t q m V r a v,j)).work+
      (run DFTModelResidualBlockXor.program
        (run (argument t) (input t q m V r a v,j)).val).work+1≤_
    rw [DFTModelResidualBlockXor.program_work,sv]
    omega
  simp only [cell,address,bank,quotient,volume,binary,input,
    run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
  dsimp only [input,run] at sw
  omega

theorem cell_valid (t : Ty) (x : (CellInput t).T) : (run (cell t) x).valid := by
  have arg : (run (argument t) x).valid := by
    rcases x with ⟨⟨⟨V,m⟩,⟨⟨N,r⟩,⟨tbl,⟨a,v⟩⟩⟩⟩,j⟩
    by_cases eq : j/V-r=0 ∧ r-j/V=0 <;>
      simp [argument,blocks,radix,table,remainder,selectedMask,difference,quotient,
        role,volume,mask,binary,run,Code.run,Atom.run,NOp.run,
        Bill.pass,Bill.pay,Bill.one,Bill.word,eq]
  have shiftedValid : (run (shifted t) x).valid :=
    ⟨arg,DFTModelResidualBlockXor.program_valid _⟩
  simpa only [cell,address,bank,quotient,volume,binary,
    run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,
    true_and,and_true] using shiftedValid

theorem program_value (t : Ty) (q m V r a : ℕ) (v : Tape t.T)
    (pos : 0 < V) (size : V ≤ 2^(q*m)) (small : a < 2^(q*m)) :
    (run (program t) (input t q m V r a v)).val=data t V r a v := by
  change (Bill.tab v.len t.blank (fun j=>run (cell t) (input t q m V r a v,j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab v.len) (funext (fun j=>cell_value t q m V r a j v pos size small))

theorem program_work (t : Ty) (q m V r a : ℕ) (v : Tape t.T) :
    (run (program t) (input t q m V r a v)).work ≤ (120*m+154)*v.len+12 := by
  change 9+(Bill.tab v.len t.blank (fun j=>run (cell t) (input t q m V r a v,j))).work+1≤_
  rw [ModelEquivalenceInterpreter.tab_work]
  have hs : (∑j∈Finset.range v.len,(run (cell t) (input t q m V r a v,j)).work)
      ≤v.len*(120*m+150) := by
    calc
      _ ≤ ∑_j∈Finset.range v.len,(120*m+150) := Finset.sum_le_sum
        (fun j _=>cell_work t q m V r a j v)
      _ = _ := by simp
  nlinarith

theorem program_valid (t : Ty) (x : (Input t).T) : (run (program t) x).valid := by
  have good : (Bill.tab x.2.2.2.2.len t.blank
    (fun j=>run (cell t) (x,j))).valid :=
    (ModelEquivalenceInterpreter.tab_valid _ _ _).2 (fun _ _=>cell_valid t _)
  simpa only [program,length,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,
    Bill.word,and_true,true_and] using good

theorem data_length (t : Ty) (V r a : ℕ) (v : Tape t.T) : (data t V r a v).len=v.len := rfl

theorem index_other (V r a j : ℕ) (other:j/V≠r) : index V r a j=j := by
  simp only [index,chosen,ite_eq_right other,Nat.xor_zero]
  have h:=Nat.mod_add_div j V
  nlinarith

theorem index_role (V r a b j : ℕ) (pos : 0 < V) (hj : j < V) :
    index V r a (b*V+j)=if b=r then b*V+(j^^^a) else b*V+j := by
  have div : (b*V+j)/V=b := by
    rw [Nat.mul_comm b V,Nat.mul_add_div pos b j,Nat.div_eq_of_lt hj,Nat.add_zero]
  have mod : (b*V+j)%V=j := by simp [Nat.add_mod,Nat.mod_eq_of_lt hj]
  simp only [index,chosen,div,mod]
  split_ifs <;> simp

end
end ExactFourierCircuits.DFTModelRecursiveYMovement

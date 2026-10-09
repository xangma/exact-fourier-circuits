import DFTModelResidualBasisMask
import UniformRepeatedMaskMachine

set_option autoImplicit false

/-! A charged repetition and mask scan of the original-width bits in an
actual Y descriptor. The raw descriptor is read, rather than supplying its
encoded direction as a program input. -/
namespace ExactFourierCircuits.DFTModelRecursiveYMask
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
noncomputable section

abbrev Input := p w (p w (p w (Ty.a w)))
abbrev CellInput := p Input w
def columns : Prog false Input w := .atom .fst
def width : Prog false Input w := .comp (.atom .snd) (.atom .fst)
def base : Prog false Input w := .comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))
def raw : Prog false Input (Ty.a w) := .comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))
def length : Prog false Input w := binary .mul columns width
def address : Prog false CellInput w := binary .add
  (binary .add (.comp (.atom .fst) base) (.atom (.lit 1)))
  (binary .mod (.atom .snd) (.comp (.atom .fst) width))
def cell : Prog false CellInput w := .comp
  (.fork (.comp (.atom .fst) raw) address) (.atom .look)
def repeated : Prog false Input (Ty.a w) := .tab length cell
def ready : Prog false Input DFTModelResidualBasisMask.Input := .fork length repeated
def program : Prog false Input w := .comp ready DFTModelResidualBasisMask.program

def input (q m A : ℕ) (v : Tape ℕ) : Input.T := (q,(m,(A,v)))
def data (q m A : ℕ) (v : Tape ℕ) : Tape ℕ :=
  Tape.tab (q*m) (fun i=>v.look (A+1+i%m) 0)

theorem length_run (q m A : ℕ) (v : Tape ℕ) :
    run length (input q m A v)=⟨q*m,7,q*m,True⟩ := by
  simp [length,columns,width,binary,input,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem cell_run (q m A i : ℕ) (v : Tape ℕ) :
    run cell (input q m A v,i)=
      ⟨v.look (A+1+i%m) 0,33,max 1 (max (A+1) (max (i%m) (A+1+i%m))),True⟩ := by
  simp [cell,address,base,width,raw,binary,input,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank,max_comm]
  omega

theorem repeated_value (q m A : ℕ) (v : Tape ℕ) :
    (run repeated (input q m A v)).val=data q m A v := by
  change (Bill.tab (q*m) w.blank (fun i=>run cell (input q m A v,i))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab (q*m)) (funext (fun i=>congrArg Bill.val (cell_run q m A i v)))

theorem repeated_work (q m A : ℕ) (v : Tape ℕ) :
    (run repeated (input q m A v)).work=37*(q*m)+10 := by
  change 7+(Bill.tab (q*m) w.blank (fun i=>run cell (input q m A v,i))).work+1=_
  rw [ModelEquivalenceInterpreter.tab_work]
  have h : (fun i=>(run cell (input q m A v,i)).work)=(fun _=>33) := by
    funext i;exact congrArg Bill.work (cell_run q m A i v)
  rw [h]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem repeated_valid (q m A : ℕ) (v : Tape ℕ) :
    (run repeated (input q m A v)).valid := by
  have h : (Bill.tab (q*m) w.blank (fun i=>run cell (input q m A v,i))).valid := by
    apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
    intro i _;rw [cell_run];trivial
  simpa only [repeated,length,columns,width,binary,input,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,and_true,true_and] using h

theorem repeated_peak (q m A : ℕ) (v : Tape ℕ) :
    (run repeated (input q m A v)).peak≤q*m+A+m+2 := by
  change (((run length (input q m A v)).pass (fun l=>
    Bill.tab l w.blank (fun i=>run cell (input q m A v,i)))).pay 1 0).peak≤_
  rw [length_run]
  change max (max (q*m) (Bill.tab (q*m) w.blank
    (fun i=>run cell (input q m A v,i))).peak) 0≤_
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp only [max_le_iff]
  refine ⟨⟨by omega,⟨by omega,?_⟩⟩,by omega⟩
  apply Finset.sup_le
  intro i hi
  have im : i % m ≤ m := by
    by_cases hm:m=0
    · subst m;simp at hi
    · exact (Nat.mod_lt i (Nat.pos_of_ne_zero hm)).le
  rw [cell_run]
  dsimp only [Bill.peak]
  omega

theorem ready_value (q m A : ℕ) (v : Tape ℕ) :
    (run ready (input q m A v)).val=(q*m,data q m A v) := by
  change ((run length (input q m A v)).val,(run repeated (input q m A v)).val)=_
  rw [length_run,repeated_value]

theorem program_value (q m A : ℕ) (v : Tape ℕ) :
    (run program (input q m A v)).val=
      DFTModelResidualBasisMask.maskPrefix (data q m A v) (q*m) := by
  change (run DFTModelResidualBasisMask.program (run ready (input q m A v)).val).val=_
  rw [ready_value,DFTModelResidualBasisMask.program_value]

theorem program_work (q m A : ℕ) (v : Tape ℕ) :
    (run program (input q m A v)).work=73*(q*m)+27 := by
  change (run length (input q m A v)).work+(run repeated (input q m A v)).work+1+
    (run DFTModelResidualBasisMask.program (run ready (input q m A v)).val).work+1=_
  rw [length_run,repeated_work,ready_value,DFTModelResidualBasisMask.program_work]
  dsimp only [Bill.work]
  omega

theorem program_valid (q m A : ℕ) (v : Tape ℕ) :
    (run program (input q m A v)).valid := by
  change ((run length (input q m A v)).valid ∧ (run repeated (input q m A v)).valid ∧ True) ∧
    (run DFTModelResidualBasisMask.program (run ready (input q m A v)).val).valid
  rw [length_run,ready_value]
  exact ⟨⟨trivial,repeated_valid q m A v,trivial⟩,DFTModelResidualBasisMask.program_valid _ _⟩

theorem source_value {m : ℕ} (q A : ℕ) (u : BinaryFrames.Vec (Fin m)) (v : Tape ℕ)
    (source : ∀i:Fin m,v.look (A+1+i.val) 0=(u i).val) :
    (run program (input q m A v)).val=
      (UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q u)).val := by
  rw [program_value,←UniformRepeatedMaskMachine.maskPrefix_direction]
  unfold DFTModelResidualBasisMask.maskPrefix UniformRepeatedMaskMachine.maskPrefix
  apply Finset.sum_congr rfl
  intro i hi
  have im:i<q*m:=Finset.mem_range.mp hi
  have mp : 0 < m :=by nlinarith only [im]
  have rem:=Nat.mod_lt i mp
  rw [Tape.look_of_lt (data q m A v) 0 im]
  change 2^i*v.look (A+1+i%m) 0=_
  rw [source ⟨i%m,rem⟩]
  simp only [UniformRepeatedMaskMachine.bits,rem,dite_eq_left]

theorem program_peak (q m A : ℕ) (v : Tape ℕ)
    (binary : ∀i:Fin m,v.look (A+1+i.val) 0<2) :
    (run program (input q m A v)).peak≤2^(q*m)+q*m+A+m+2 := by
  have bits : ∀i,i<q*m→(data q m A v).look i 0<2 := by
    intro i hi
    have mp : 0 < m :=by nlinarith only [hi]
    have rem:=Nat.mod_lt i mp
    simpa only [data,Tape.look,Tape.tab,hi,dite_eq_left] using binary ⟨i%m,rem⟩
  have mask:=DFTModelResidualBasisMask.program_peak (q*m) (data q m A v) bits
  have rep:=repeated_peak q m A v
  change max (max (max (run length (input q m A v)).peak
    (max (run repeated (input q m A v)).peak 0))
    (run DFTModelResidualBasisMask.program (run ready (input q m A v)).val).peak) 0≤_
  rw [length_run,ready_value]
  dsimp only [Bill.peak]
  simp only [max_zero]
  apply max_le
  · apply max_le
    · omega
    · apply rep.trans
      simpa only [Nat.add_assoc] using
        (Nat.le_add_left (q*m+A+m+2) (2^(q*m)))
  · exact mask.trans (by omega)

end
end ExactFourierCircuits.DFTModelRecursiveYMask

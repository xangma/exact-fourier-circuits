import ModelEquivalenceInterpreter

set_option autoImplicit false

/-! A closed upstream typed-RAM producer for physical CRT tables.  Each axis
recurses once, then allocates one enlarged Cartesian table.  The initial tapes
contain radix/weight metadata, never a precomputed permutation or callback. -/
namespace ExactFourierCircuits.DFTModelCRT
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Entry := p w w
abbrev Row := p w Entry
abbrev Args := p w (p w (a Row))
abbrev ExtendInput := p Args (a Entry)
abbrev CellInput := p ExtendInput w

def nat {s : Ty} (op : NOp) (f g : Prog false s w) : Prog false s w :=
  .comp (.fork f g) (.atom (.int op))

def row : Prog false Args Row :=
  .comp (.fork (.comp (.atom .snd) (.atom .snd)) (.atom .fst)) (.atom .look)

def next : Prog false Args Args :=
  .fork (nat .add (.atom .fst) (.atom (.lit 1))) (.atom .snd)

def cellArgs : Prog false CellInput Args := .comp (.atom .fst) (.atom .fst)
def old : Prog false CellInput (a Entry) := .comp (.atom .fst) (.atom .snd)
def oldLength : Prog false CellInput w := .comp old (.atom .len)
def oldIndex : Prog false CellInput w := nat .mod (.atom .snd) oldLength
def oldEntry : Prog false CellInput Entry := .comp (.fork old oldIndex) (.atom .look)
def digit : Prog false CellInput w := nat .div (.atom .snd) oldLength
def cellRow : Prog false CellInput Row := .comp cellArgs row
def volume : Prog false CellInput w := .comp cellArgs (.comp (.atom .snd) (.atom .fst))
def alphaWeight : Prog false CellInput w :=
  .comp cellRow (.comp (.atom .snd) (.atom .fst))
def betaWeight : Prog false CellInput w :=
  .comp cellRow (.comp (.atom .snd) (.atom .snd))

def alphaCell : Prog false CellInput w :=
  nat .mod (nat .add (.comp oldEntry (.atom .fst)) (nat .mul digit alphaWeight)) volume
def betaCell : Prog false CellInput w :=
  nat .mod (nat .add (.comp oldEntry (.atom .snd)) (nat .mul digit betaWeight)) volume
def cell : Prog false CellInput Entry := .fork alphaCell betaCell

def extendedLength : Prog false ExtendInput w :=
  nat .mul (.comp (.atom .fst) (.comp row (.atom .fst)))
    (.comp (.atom .snd) (.atom .len))
def extend : Prog false ExtendInput (a Entry) := .tab extendedLength cell

def base : Prog false Args (a Entry) :=
  .tab (.atom (.lit 1)) (.fork (.atom (.lit 0)) (.atom (.lit 0)))

def step : Code false (some (Args,a Entry)) Args (a Entry) :=
  .comp (.fork (.atom .id) (.comp (.importClosed next) .call)) (.importClosed extend)

def tables : Prog false (p w Args) (a Entry) := .descend base step

def alpha : Prog false (a Entry) (a w) :=
  .tab (.atom .len) (.comp (.atom .look) (.atom .fst))
def inverseBeta : Prog false (a Entry) (a w) :=
  .sow (.atom .len) (.atom .len)
    (.fork (.comp (.atom .look) (.atom .snd)) (.atom .snd))

/-- AP and inverse-Beta, produced using only integer atoms and fresh arrays. -/
def program : Prog false (p w Args) (p (a w) (a w)) :=
  .comp tables (.fork alpha inverseBeta)

def readRow (x : Args.T) : ℕ × (ℕ × ℕ) := x.2.2.look x.1 (0,(0,0))
def successor (x : Args.T) : Args.T := (x.1+1,x.2)
def valueCell (x : Args.T) (t : Tape (ℕ × ℕ)) (j : ℕ) : ℕ × ℕ :=
  (((t.look (j%t.len) (0,0)).1+(j/t.len)*(readRow x).2.1)%x.2.1,
   ((t.look (j%t.len) (0,0)).2+(j/t.len)*(readRow x).2.2)%x.2.1)
def enlarged (x : Args.T) (t : Tape (ℕ × ℕ)) : Tape (ℕ × ℕ) :=
  Tape.tab ((readRow x).1*t.len) (valueCell x t)

theorem next_run (x : Args.T) : run next x = ⟨successor x,7,1+x.1,True⟩ := by
  simp [next,nat,successor,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,Nat.add_comm]

theorem cell_value (x : Args.T) (t : Tape (ℕ × ℕ)) (j : ℕ) :
    (run cell ((x,t),j)).val = valueCell x t j := by
  simp [cell,alphaCell,betaCell,nat,oldEntry,oldIndex,old,oldLength,digit,
    alphaWeight,betaWeight,cellRow,row,cellArgs,volume,readRow,valueCell,
    run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]

theorem cell_work (x : Args.T) (t : Tape (ℕ × ℕ)) (j : ℕ) :
    (run cell ((x,t),j)).work = 115 := by
  simp [cell,alphaCell,betaCell,nat,oldEntry,oldIndex,old,oldLength,digit,
    alphaWeight,betaWeight,cellRow,row,cellArgs,volume,
    run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]

theorem cell_valid (x : Args.T) (t : Tape (ℕ × ℕ)) (j : ℕ) :
    (run cell ((x,t),j)).valid := by
  simp [cell,alphaCell,betaCell,nat,oldEntry,oldIndex,old,oldLength,digit,
    alphaWeight,betaWeight,cellRow,row,cellArgs,volume,
    run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]

theorem extendedLength_run (x : Args.T) (t : Tape (ℕ × ℕ)) :
    run extendedLength (x,t) = ⟨(readRow x).1*t.len,17,
      max t.len ((readRow x).1*t.len),True⟩ := by
  simp [extendedLength,nat,row,readRow,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]

theorem extend_value (x : Args.T) (t : Tape (ℕ × ℕ)) :
    (run extend (x,t)).val = enlarged x t := by
  change (Bill.tab (run extendedLength (x,t)).val Entry.blank
    (fun j => run cell ((x,t),j))).val = _
  rw [extendedLength_run,ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab _) (funext (cell_value x t))

theorem extend_work (x : Args.T) (t : Tape (ℕ × ℕ)) :
    (run extend (x,t)).work = 119*((readRow x).1*t.len)+20 := by
  change (run extendedLength (x,t)).work+
    (Bill.tab (run extendedLength (x,t)).val Entry.blank
      (fun j => run cell ((x,t),j))).work+1 = _
  rw [extendedLength_run,ModelEquivalenceInterpreter.tab_work]
  change 17+(2+4*((readRow x).1*t.len)+
    ∑ j ∈ Finset.range ((readRow x).1*t.len), (run cell ((x,t),j)).work)+1 = _
  have hc : (fun j => (run cell ((x,t),j)).work) = (fun _ => 115) :=
    funext (cell_work x t)
  rw [hc]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem extend_valid (x : Args.T) (t : Tape (ℕ × ℕ)) :
    (run extend (x,t)).valid := by
  change (run extendedLength (x,t)).valid ∧
    (Bill.tab (run extendedLength (x,t)).val Entry.blank
      (fun j => run cell ((x,t),j))).valid
  rw [extendedLength_run]
  exact ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2
    (fun j _ => cell_valid x t j)⟩

theorem base_value (x : Args.T) : (run base x).val = Tape.tab 1 (fun _ => (0,0)) := by
  change (Bill.tab 1 Entry.blank (fun _ => Bill.one (0,0) |>.pay 2 0)).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  rfl

theorem base_work (x : Args.T) : (run base x).work = 11 := by
  simp [base,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word,
    Bill.tab,Bill.sow,Bill.steps,Ty.blank]

end
end ExactFourierCircuits.DFTModelCRT

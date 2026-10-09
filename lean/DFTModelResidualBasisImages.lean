import DFTModelResidualBasisPivot
import UniformResidualGeneralPreparation

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelResidualBasisImages
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
noncomputable section

/-- q columns, native block width m, spectator count r, actual mask and pivot. -/
abbrev Params := p w (p w (p w (p w w)))
abbrev Input := p Params w

def columns : Prog false Params w := .atom .fst
def width : Prog false Params w := .comp (.atom .snd) (.atom .fst)
def spectators : Prog false Params w := .comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))
def mask : Prog false Params w := .comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def pivot : Prog false Params w := .comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))
def fromParams (f : Prog false Params w) : Prog false Input w := .comp (.atom .fst) f

def lowerCount : Prog false Params w := binary .mul columns width
def count : Prog false Params w := binary .add lowerCount spectators

def repIndex : Prog false Input w := binary .sub (.atom .snd) (fromParams columns)
def repWidth : Prog false Input w := binary .sub (fromParams width) (.atom (.lit 1))
def col : Prog false Input w := binary .div repIndex repWidth
def adjacent : Prog false Input w := binary .mod repIndex repWidth
def omitted : Prog false Input w := .ifz (binary .lt adjacent (fromParams pivot))
  (binary .add adjacent (.atom (.lit 1))) adjacent

def selectedExponent : Prog false Input w := binary .mul (.atom .snd) (fromParams width)
def repExponent : Prog false Input w := binary .add
  (binary .mul col (fromParams width)) omitted

def exponent : Prog false Input w := .ifz (binary .lt (.atom .snd) (fromParams columns))
  (.ifz (binary .lt (.atom .snd) (fromParams lowerCount)) (.atom .snd) repExponent)
  selectedExponent

def multiplier : Prog false Input w := .ifz (binary .lt (.atom .snd) (fromParams columns))
  (.atom (.lit 1)) (fromParams mask)

/-- Every image is physically computed, including its power of two. -/
def cell : Prog false Input w := binary .mul (.comp exponent power) multiplier
def program : Prog false Params (Ty.a w) := .tab count cell

def exponentValue (q m p i : ℕ) : ℕ :=
  if i<q then i*m else if i<q*m then
    ((i-q)/(m-1))*m+(if (i-q)%(m-1)<p then (i-q)%(m-1) else (i-q)%(m-1)+1)
  else i

def imageValue (q m mask p i : ℕ) : ℕ :=
  2^(exponentValue q m p i)*(if i<q then mask else 1)

attribute [local irreducible] power

theorem exponent_value (q m r a p i : ℕ) :
    (run exponent ((q,(m,(r,(a,p)))),i)).val=exponentValue q m p i := by
  by_cases lo:i<q <;> by_cases hi:i<q*m <;> by_cases adj:(i-q)%(m-1)<p <;>
    simp [exponent,selectedExponent,repExponent,omitted,adjacent,col,repIndex,repWidth,
      fromParams,columns,width,pivot,lowerCount,binary,exponentValue,run,Code.run,
      Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,lo,hi,adj]

theorem exponent_work (q m r a p i : ℕ) :
    (run exponent ((q,(m,(r,(a,p)))),i)).work≤150 := by
  by_cases lo:i<q <;> by_cases hi:i<q*m <;> by_cases adj:(i-q)%(m-1)<p <;>
    simp [exponent,selectedExponent,repExponent,omitted,adjacent,col,repIndex,repWidth,
      fromParams,columns,width,pivot,lowerCount,binary,run,Code.run,
      Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,lo,hi,adj]

theorem multiplier_run (q m r a p i : ℕ) :
    run multiplier ((q,(m,(r,(a,p)))),i)=
      ⟨if i<q then a else 1,if i<q then 17 else 9,1,True⟩ := by
  by_cases lo:i<q <;>
    simp [multiplier,fromParams,columns,mask,binary,run,Code.run,
      Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,lo]

theorem cell_value (q m r a p i : ℕ) :
    (run cell ((q,(m,(r,(a,p)))),i)).val=imageValue q m a p i := by
  change (run power (run exponent ((q,(m,(r,(a,p)))),i)).val).val*
    (run multiplier ((q,(m,(r,(a,p)))),i)).val=_
  rw [power_value,exponent_value,multiplier_run]
  rfl

theorem cell_work (q m r a p i : ℕ) :
    (run cell ((q,(m,(r,(a,p)))),i)).work≤8*exponentValue q m p i+200 := by
  rw [cell,binary_work]
  change (run exponent ((q,(m,(r,(a,p)))),i)).work+
    (run power (run exponent ((q,(m,(r,(a,p)))),i)).val).work+1+
    (run multiplier ((q,(m,(r,(a,p)))),i)).work+3≤_
  rw [power_work,exponent_value,multiplier_run]
  have ex:=exponent_work q m r a p i
  split_ifs <;> dsimp only [Bill.work] <;> omega

theorem cell_valid (q m r a p i : ℕ) :
    (run cell ((q,(m,(r,(a,p)))),i)).valid := by
  have ex:(run exponent ((q,(m,(r,(a,p)))),i)).valid := by
    by_cases lo:i<q <;> by_cases hi:i<q*m <;> by_cases adj:(i-q)%(m-1)<p <;>
      simp [exponent,selectedExponent,repExponent,omitted,adjacent,col,repIndex,repWidth,
        fromParams,columns,width,pivot,lowerCount,binary,run,Code.run,
        Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,lo,hi,adj]
  rw [cell,binary_valid]
  exact ⟨⟨ex,power_valid _⟩,by rw [multiplier_run];trivial⟩

theorem count_run (q m r a p : ℕ) :
    run count (q,(m,(r,(a,p))))=⟨q*m+r,15,max (q*m+r) (max (q*m) 0),True⟩ := by
  simp [count,lowerCount,columns,width,spectators,binary,run,Code.run,
    Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem program_value (q m r a p : ℕ) :
    (run program (q,(m,(r,(a,p))))).val=
      Tape.tab (q*m+r) (imageValue q m a p) := by
  change (Bill.tab (run count (q,(m,(r,(a,p))))).val w.blank
    (fun i=>run cell ((q,(m,(r,(a,p)))),i))).val=_
  rw [count_run,ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab (q*m+r)) (funext (cell_value q m r a p))

theorem program_valid (q m r a p : ℕ) :
    (run program (q,(m,(r,(a,p))))).valid := by
  change (run count (q,(m,(r,(a,p))))).valid ∧
    (Bill.tab (run count (q,(m,(r,(a,p))))).val w.blank
      (fun i=>run cell ((q,(m,(r,(a,p)))),i))).valid
  rw [count_run]
  exact ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2
    (fun i _=>cell_valid q m r a p i)⟩

end
end ExactFourierCircuits.DFTModelResidualBasisImages

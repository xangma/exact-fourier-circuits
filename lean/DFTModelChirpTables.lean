import DFTModelChirpCorrect
import DFTModelIntegerScalar
import UniformNormalizationPreparation

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelChirpTables
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Input := p (p w w) sc
abbrev Full := p (p w w) (Ty.a sc)
abbrev Cell := p Full w
abbrev Output := p (Ty.a sc) (p (Ty.a sc) (p (Ty.a sc) (p (Ty.a sc) sc)))

def count : Prog false Full w := .comp (.atom .fst) (.atom .fst)
def width : Prog false Full w := .comp (.atom .fst) (.atom .snd)
def cellCount : Prog false Cell w := .comp (.atom .fst) count
def cellWidth : Prog false Cell w := .comp (.atom .fst) width
def firstIndex : Prog false Cell w :=
  .comp (.fork (.atom .snd) (.atom (.lit 2))) (.atom (.int .mul))
def inverseIndex : Prog false Cell w :=
  .comp (.fork firstIndex (.atom (.lit 1))) (.atom (.int .add))
def distance : Prog false Cell w :=
  .comp (.fork cellWidth (.atom .snd)) (.atom (.int .sub))
def distantIndex : Prog false Cell w :=
  .comp (.fork
    (.comp (.fork distance (.atom (.lit 2))) (.atom (.int .mul)))
    (.atom (.lit 1))) (.atom (.int .add))
def positive : Prog false Cell w :=
  .comp (.fork (.atom .snd) cellCount) (.atom (.int .lt))
def negative : Prog false Cell w :=
  .comp (.fork distance cellCount) (.atom (.int .lt))
def read (ix : Prog false Cell w) : Prog false Cell sc :=
  .comp (.fork (.comp (.atom .fst) (.atom .snd)) ix) (.atom .look)
def forwardCell : Prog false Cell sc := read firstIndex
def inputCell : Prog false Cell sc := .ifz positive (.atom (.cz .scalar)) forwardCell
def kernelCell : Prog false Cell sc :=
  .ifz positive (.ifz negative (.atom (.cz .scalar)) (read distantIndex)) (read inverseIndex)

def outputTable : Prog false Full (Ty.a sc) := .tab count forwardCell
def inputTable : Prog false Full (Ty.a sc) := .tab width inputCell
def kernelTable : Prog false Full (Ty.a sc) := .tab width kernelCell
def normalization : Prog false Full sc := .comp width DFTModelIntegerScalar.reciprocal

def publish : Prog false Full Output :=
  .fork (.atom .snd)
    (.fork outputTable (.fork inputTable (.fork kernelTable normalization)))

def setup : Prog false Input Full :=
  .fork (.atom .fst)
    (.comp (.fork (.comp (.atom .fst) (.atom .fst)) (.atom .snd)) DFTModelChirp.program)

/-- Computes every coefficient from the length and supplied half-angle root. -/
def program : Prog false Input Output := .comp setup publish

def forward (v : Tape ℂ) (i : ℕ) : ℂ := v.look (2*i) 0
def inputValue (n : ℕ) (v : Tape ℂ) (i : ℕ) : ℂ :=
  if i<n then forward v i else 0
def kernelValue (n L : ℕ) (v : Tape ℂ) (i : ℕ) : ℂ :=
  if i<n then v.look (2*i+1) 0
  else if L-i<n then v.look (2*(L-i)+1) 0 else 0

theorem forwardCell_run (n L i : ℕ) (v : Tape ℂ) :
    run forwardCell (((n,L),v),i) = ⟨forward v i,11,max 2 (2*i),True⟩ := by
  simp [forwardCell,read,firstIndex,forward,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank,Nat.mul_comm]

theorem inputCell_spec (n L i : ℕ) (v : Tape ℂ) :
    (run inputCell (((n,L),v),i)).val = inputValue n v i ∧
    (run inputCell (((n,L),v),i)).work ≤ 30 ∧
    (run inputCell (((n,L),v),i)).peak ≤ 2*i+2 ∧
    (run inputCell (((n,L),v),i)).valid := by
  by_cases hi : i<n
  · simp [inputCell,positive,cellCount,count,forwardCell,read,firstIndex,inputValue,forward,
      Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,hi,Ty.blank,Nat.mul_comm]
  · simp [inputCell,positive,cellCount,count,inputValue,
      Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,hi]

theorem kernelCell_spec (n L i : ℕ) (v : Tape ℂ) :
    (run kernelCell (((n,L),v),i)).val = kernelValue n L v i ∧
    (run kernelCell (((n,L),v),i)).work ≤ 60 ∧
    (run kernelCell (((n,L),v),i)).peak ≤ 2*(L+i)+2 ∧
    (run kernelCell (((n,L),v),i)).valid := by
  by_cases hi : i<n
  · simp [kernelCell,positive,cellCount,count,read,inverseIndex,firstIndex,kernelValue,
      Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,hi,Ty.blank,Nat.mul_comm]
    omega
  · by_cases hd : L-i<n
    · simp [kernelCell,positive,negative,cellCount,cellWidth,count,width,distance,
        read,distantIndex,kernelValue,Code.run,Atom.run,NOp.run,
        Bill.pass,Bill.pay,Bill.one,Bill.word,hi,hd,Ty.blank,Nat.mul_comm]
      omega
    · simp [kernelCell,positive,negative,cellCount,cellWidth,count,width,distance,kernelValue,
        Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,hi,hd]
      omega

end
end ExactFourierCircuits.DFTModelChirpTables

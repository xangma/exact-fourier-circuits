import DFTModelCacheColorPolynomial

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheColorRebase
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheColor (Row nat)
open DFTModelRecursiveScalarCore
noncomputable section
abbrev Input := p w DFTModelCacheColor.Input
abbrev Cell := p Input w
def rows : Prog false Input (Ty.a Row) := .comp (.atom .snd) (.atom .snd)
def count : Prog false Input w := .comp rows (.atom .len)
def localBound : Prog false Input w := .comp (.atom .snd) (.atom .fst)
def base : Prog false Cell w := .comp (.atom .fst) (.atom .fst)
def row : Prog false Cell Row := .comp (.fork (.comp (.atom .fst) rows) (.atom .snd)) (.atom .look)
/-- Only endpoint coordinates are rebased. The physical coefficient address is
retained verbatim, even when it is zero or duplicated. -/
def rebaseRow : Prog false Cell Row := .fork
 (nat .sub (.comp row (.atom .fst)) base)
 (.fork (nat .sub (.comp row (.comp (.atom .snd) (.atom .fst))) base)
   (.comp row (.comp (.atom .snd) (.atom .snd))))
def prepare : Prog false Input DFTModelCacheColor.Input :=
 .fork localBound (.tab count rebaseRow)
def program : Prog false Input (p Input (p DFTModelCacheColor.Input DFTModelCacheColor.Output)) :=
 .fork (.atom .id) (.comp prepare DFTModelCacheColor.program)

def rebaseValue (A : ℕ) (z : Tape Row.T) (j : ℕ) : Row.T :=
 let physical:=z.look j Row.blank
 (physical.1-A,(physical.2.1-A,physical.2.2))
def localRows (A : ℕ) (z : Tape Row.T) : Tape Row.T := Tape.tab z.len (rebaseValue A z)

theorem rebaseRow_run (A r : ℕ) (z : Tape Row.T) (j : ℕ) :
 run rebaseRow ((A,(r,z)),j)=⟨rebaseValue A z j,51,
  max ((z.look j Row.blank).1-A) ((z.look j Row.blank).2.1-A),True⟩ := by
 simp [rebaseRow,row,rows,base,nat,DFTModelCacheMatchingNat.nat,
  run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,rebaseValue]

theorem count_run (A r : ℕ) (z : Tape Row.T) : run count (A,(r,z))=⟨z.len,5,z.len,True⟩ := by
 simp [count,rows,run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay]

theorem prepare_value (A r : ℕ) (z : Tape Row.T) :
 (run prepare (A,(r,z))).val=(r,localRows A z) := by
 rw [prepare,DFTModelCacheMatchingNat.fork_value,DFTModelCacheMatchingNat.tab_value_code,count_run]
 change (r,_)=(r,_)
 exact congrArg (fun t=>(r,t)) (congrArg (Tape.tab z.len)
  (funext (fun j=>congrArg Bill.val (rebaseRow_run A r z j))))

end
end ExactFourierCircuits.DFTModelCacheColorRebase

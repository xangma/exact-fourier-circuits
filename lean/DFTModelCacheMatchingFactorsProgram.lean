import DFTModelCacheMatchingFactorsScalar
import DFTModelCRTInverse
import DFTModelResidualMovement

set_option autoImplicit false

/-! A literal linear-work scatter. Permutation and coefficient-pair tapes are
already-produced readonly inputs; no factor function or selector is an input. -/
namespace ExactFourierCircuits.DFTModelCacheMatchingFactors
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section
attribute [local irreducible] scalar

abbrev Input := p w (p (Ty.a w) (p (Ty.a (p sc sc)) (p sc sc)))
abbrev Cell := p Input w

def radix : Prog false Cell w := .comp (.atom .fst) (.atom .fst)
def position : Prog false Cell w :=
  .comp (.fork (.atom .snd) radix) (.atom (.int .mod))
def laneIndex : Prog false Cell w :=
  .comp (.fork (.atom .snd) radix) (.atom (.int .div))
def rowIndex : Prog false Cell w :=
  .comp (.fork position (.atom (.lit 2))) (.atom (.int .div))
def sideIndex : Prog false Cell w :=
  .comp (.fork position (.atom (.lit 2))) (.atom (.int .mod))
def pairs : Prog false Cell (Ty.a (p sc sc)) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def suppliedConstants : Prog false Cell (p sc sc) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))
def permutation : Prog false Cell (Ty.a w) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def pairAt : Prog false Cell (p sc sc) := .comp (.fork pairs rowIndex) (.atom .look)
def scalarArgument : Prog false Cell FactorInput :=
  .fork (.fork laneIndex sideIndex) (.fork pairAt suppliedConstants)
def rowCount : Prog false Cell w := .comp pairs (.atom .len)
def inPairs : Prog false Cell w := .comp (.fork rowIndex rowCount) (.atom (.int .lt))
def packedCell : Prog false Cell sc :=
  .ifz inPairs (.atom .cone) (.comp scalarArgument scalar)
def destination : Prog false Cell w :=
  .comp (.fork (.comp (.fork laneIndex radix) (.atom (.int .mul)))
    (.comp (.fork permutation position) (.atom .look))) (.atom (.int .add))
def cell : Prog false Cell (p w sc) := .fork destination packedCell
def length : Prog false Input w :=
  .comp (.fork (.atom (.lit 9)) (.atom .fst)) (.atom (.int .mul))
def program : Prog false Input (Ty.a sc) := .sow length length cell

def args (r : ℕ) (p : Tape ℕ) (z : Tape (ℂ × ℂ)) (i ai : ℂ) : Input.T :=
  (r,(p,(z,(i,ai))))
def pairArgs (r : ℕ) (z : Tape (ℂ × ℂ)) (i ai : ℂ) (j : ℕ) : FactorInput.T :=
  ((j/r,j%r%2),(z.look (j%r/2) (0,0),(i,ai)))
def packedValue (r : ℕ) (z : Tape (ℂ × ℂ)) (i ai : ℂ) (j : ℕ) : ℂ :=
  if j%r/2<z.len then (run scalar (pairArgs r z i ai j)).val else 1

theorem scalarArgument_run (r j : ℕ) (p : Tape ℕ) (z : Tape (ℂ × ℂ)) (i ai : ℂ) :
    run scalarArgument (args r p z i ai,j)=
      ⟨pairArgs r z i ai j,49,max (j/r) (max 2 (max (j%r) (j%r/2))),True⟩ := by
  simp [scalarArgument,pairAt,laneIndex,sideIndex,rowIndex,position,radix,pairs,
    suppliedConstants,args,pairArgs,run,Code.run,Atom.run,NOp.run,
    Bill.word,Bill.one,Bill.pass,Bill.pay,Ty.blank]
  omega

theorem inPairs_run (r j : ℕ) (p : Tape ℕ) (z : Tape (ℂ × ℂ)) (i ai : ℂ) :
    run inPairs (args r p z i ai,j)=
      ⟨if j%r/2<z.len then 1 else 0,23,
        max (max 2 (max (j%r) (j%r/2))) (max z.len (if j%r/2<z.len then 1 else 0)),True⟩ := by
  simp [inPairs,rowIndex,rowCount,pairs,position,radix,args,run,Code.run,Atom.run,NOp.run,
    Bill.word,Bill.one,Bill.pass,Bill.pay]
  omega

theorem destination_run (r j : ℕ) (p : Tape ℕ) (z : Tape (ℂ × ℂ)) (i ai : ℂ) :
    run destination (args r p z i ai,j)=
      ⟨j/r*r+p.look (j%r) 0,31,
        max (max (j/r) (j/r*r)) (max (j%r) (j/r*r+p.look (j%r) 0)),True⟩ := by
  simp [destination,laneIndex,radix,permutation,position,args,run,Code.run,Atom.run,NOp.run,
    Bill.word,Bill.one,Bill.pass,Bill.pay,Ty.blank]

theorem length_run (r : ℕ) (p : Tape ℕ) (z : Tape (ℂ × ℂ)) (i ai : ℂ) :
    run length (args r p z i ai)=⟨9*r,5,max 9 (9*r),True⟩ := by
  simp [length,args,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]

def argumentPeak (r : ℕ) (z : Tape (ℂ × ℂ)) (j : ℕ) : ℕ :=
  max (j/r) (max 2 (max (j%r) (max (j%r/2) z.len)))

theorem packedCell_yes (r j : ℕ) (p : Tape ℕ) (z : Tape (ℂ × ℂ)) (i ai : ℂ)
    (h : j%r/2<z.len) :
    run packedCell (args r p z i ai,j)=
      (run scalar (pairArgs r z i ai j)).pay 74 (argumentPeak r z j) := by
  rw [packedCell,ifz_run,inPairs_run]
  simp only [h,ite_true]
  rw [comp_run,scalarArgument_run]
  simp [Bill.pass,Bill.pay,argumentPeak]
  omega

theorem packedCell_no (r j : ℕ) (p : Tape ℕ) (z : Tape (ℂ × ℂ)) (i ai : ℂ)
    (h : ¬j%r/2<z.len) :
    run packedCell (args r p z i ai,j)=
      ⟨1,25,max 2 (max (j%r) (max (j%r/2) z.len)),True⟩ := by
  rw [packedCell,ifz_run,inPairs_run]
  simp [h,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

theorem packedCell_value (r j : ℕ) (p : Tape ℕ) (z : Tape (ℂ × ℂ)) (i ai : ℂ) :
    (run packedCell (args r p z i ai,j)).val=packedValue r z i ai j := by
  by_cases h:j%r/2<z.len
  · rw [packedCell_yes _ _ _ _ _ _ h]
    exact (ite_eq_left h).symm
  · rw [packedCell_no _ _ _ _ _ _ h]
    exact (ite_eq_right h).symm

theorem cell_value (r j : ℕ) (p : Tape ℕ) (z : Tape (ℂ × ℂ)) (i ai : ℂ) :
    (run cell (args r p z i ai,j)).val=
      (j/r*r+p.look (j%r) 0,packedValue r z i ai j) := by
  rw [cell,fork_run,destination_run]
  simp only [Bill.pass,Bill.one]
  rw [packedCell_value]

theorem cell_run (r j : ℕ) (p : Tape ℕ) (z : Tape (ℂ × ℂ)) (i ai : ℂ) :
    run cell (args r p z i ai,j)=
      ⟨(j/r*r+p.look (j%r) 0,(run packedCell (args r p z i ai,j)).val),
        (run packedCell (args r p z i ai,j)).work+32,
        max (max (max (j/r) (j/r*r)) (max (j%r) (j/r*r+p.look (j%r) 0)))
          (run packedCell (args r p z i ai,j)).peak,
        (run packedCell (args r p z i ai,j)).valid⟩ := by
  rw [cell,fork_run,destination_run]
  simp [Bill.pass,Bill.one]
  omega

theorem program_run (r : ℕ) (p : Tape ℕ) (z : Tape (ℂ × ℂ)) (i ai : ℂ) :
    run program (args r p z i ai)=
      (Bill.sow (9*r) (9*r) 0 (fun j=>run cell (args r p z i ai,j))).pay 11 (max 9 (9*r)) := by
  change ((run length (args r p z i ai)).pass (fun L=>
    (run length (args r p z i ai)).pass (fun C=>
      Bill.sow L C sc.blank (fun j=>run cell (args r p z i ai,j))))).pay 1 0=_
  rw [length_run]
  simp [Bill.pass,Bill.pay,Ty.blank]
  omega

theorem program_value (r : ℕ) (p : Tape ℕ) (z : Tape (ℂ × ℂ)) (i ai : ℂ) :
    (run program (args r p z i ai)).val=
      Tape.sow (9*r) (9*r) 0 (fun j=>
        (j/r*r+p.look (j%r) 0,packedValue r z i ai j)) := by
  rw [program_run]
  change (Bill.sow _ _ _ _).val=_
  rw [DFTModelCRT.sow_value]
  exact congrArg (Tape.sow (9*r) (9*r) 0) (funext (fun j=>cell_value r j p z i ai))

theorem program_length (r : ℕ) (p : Tape ℕ) (z : Tape (ℂ × ℂ)) (i ai : ℂ) :
    (run program (args r p z i ai)).val.len=9*r := by
  rw [program_value]
  exact DFTModelCRT.sow_iter_len _ _ _ _

end
end ExactFourierCircuits.DFTModelCacheMatchingFactors

import DFTModelOuterTailOutput

set_option autoImplicit false

/-! One closed upstream typed program for the actual last three stages.
It executes BI and AP once each, retains both banks, then tabulates output
from the BI bank. Prepared coefficient/normalization provenance is an entry
contract; no field action, execution or cost callback is supplied. -/
namespace ExactFourierCircuits.DFTModelOuterTail
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Datum := DFTModelAffine.Tagged
abbrev Params := p w (p (Ty.a sc) sc)
abbrev Input := p DFTModelOuterTailCRT.Input Params
abbrev Output := p DFTModelOuterTailCRT.Output (Ty.a Datum)
abbrev Joined := p Input DFTModelOuterTailCRT.Output
def count : Prog false Joined w :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def width : Prog false Joined w :=
  .comp (.atom .fst) (.comp (.atom .fst) (.atom .fst))
def coefficients : Prog false Joined (Ty.a sc) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def normalization : Prog false Joined sc :=
  .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))
def betaBank : Prog false Joined (Ty.a Datum) := .comp (.atom .snd) (.atom .snd)
def output : Prog false Joined (Ty.a Datum) :=
  .comp (.fork (.fork count width) (.fork coefficients (.fork normalization betaBank)))
    DFTModelOuterTailOutput.program
def program : Prog false Input Output :=
  .comp (.fork (.atom .id) (.comp (.atom .fst) DFTModelOuterTailCRT.program))
    (.fork (.atom .snd) output)

def input (n V : ℕ) (a b : Tape ℕ) (c : Tape ℂ) (k : ℂ) (z : Tape Datum.T) : Input.T :=
  (DFTModelOuterTailCRT.input V a b z,(n,(c,k)))

attribute [local irreducible] DFTModelOuterTailCRT.program DFTModelOuterTailOutput.program
theorem program_run (n V : ℕ) (a b : Tape ℕ) (c : Tape ℂ) (k : ℂ) (z : Tape Datum.T) :
    run program (input n V a b c k z) =
      ((run DFTModelOuterTailCRT.program (DFTModelOuterTailCRT.input V a b z)).pass
        (fun t => (run DFTModelOuterTailOutput.program
          (DFTModelOuterTailOutput.input n V c k t.2)).pass (fun o => Bill.one (t,o)))).pay 38 0 := by
  simp only [program,output,count,width,coefficients,normalization,betaBank,input,
    DFTModelOuterTailCRT.input,DFTModelOuterTailOutput.input,run,Code.run,Atom.run,
    Bill.pass,Bill.pay,Bill.one]
  simp only [zero_max,max_zero,true_and,and_true]
  congr 1
  · omega

theorem program_value (n V : ℕ) (a b : Tape ℕ) (c : Tape ℂ) (k : ℂ) (z : Tape Datum.T) :
    (run program (input n V a b c k z)).val =
      ((DFTModelOuterTailCRT.gatherValue V a (DFTModelOuterTailCRT.gatherValue V b z),
        DFTModelOuterTailCRT.gatherValue V b z),
       Tape.tab n (fun j => DFTModelOuterTailOutput.value V j c k
         (DFTModelOuterTailCRT.gatherValue V b z))) := by
  rw [program_run]
  simp only [Bill.pass,Bill.pay,Bill.one]
  rw [DFTModelOuterTailCRT.program_value,DFTModelOuterTailOutput.program_value]

theorem program_valid (n V : ℕ) (a b : Tape ℕ) (c : Tape ℂ) (k : ℂ) (z : Tape Datum.T) :
    (run program (input n V a b c k z)).valid := by
  rw [program_run]
  exact ⟨DFTModelOuterTailCRT.program_valid _ _ _ _,
    DFTModelOuterTailOutput.program_valid _ _ _ _ _,trivial⟩

theorem program_work (n V : ℕ) (a b : Tape ℕ) (c : Tape ℂ) (k : ℂ) (z : Tape Datum.T) :
    (run program (input n V a b c k z)).work = 42*V+105*n+84 := by
  rw [program_run]
  simp only [Bill.pass,Bill.pay,Bill.one]
  rw [DFTModelOuterTailCRT.program_work,DFTModelOuterTailOutput.program_work]
  omega

theorem program_peak (n V : ℕ) (a b : Tape ℕ) (c : Tape ℂ) (k : ℂ) (z : Tape Datum.T) :
    (run program (input n V a b c k z)).peak ≤ max V (2*n) := by
  rw [program_run]
  simp only [Bill.pass,Bill.pay,Bill.one]
  rw [DFTModelOuterTailCRT.program_peak]
  have h := DFTModelOuterTailOutput.program_peak n V c k
    (run DFTModelOuterTailCRT.program (DFTModelOuterTailCRT.input V a b z)).val.2
  omega

/-- The same actual local ticks proved for stages 18–20, with a fixed factor. -/
theorem work_preserved (n V : ℕ) (a b : Tape ℕ) (c : Tape ℂ) (k : ℂ) (z : Tape Datum.T) :
    (run program (input n V a b c k z)).work ≤ 9*(18*V+13*n+36) := by
  rw [program_work]
  omega

end
end ExactFourierCircuits.DFTModelOuterTail

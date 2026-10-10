import DFTModelOuterTailCRT
import DFTModelAffinePaired

set_option autoImplicit false

/-! Paper §5.3, PDF p.23: the actual input AP gather. Header7312 denotes
padded input; saved prepared spectrum7300 is retained separately. -/
namespace ExactFourierCircuits.DFTModelOuterAlpha
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Datum := DFTModelAffine.Tagged
abbrev Input := p DFTModelOuterTailCRT.GatherInput (p (Ty.a Datum) (Ty.a sc))
abbrev Output := p (Ty.a Datum) Input

def program : Prog false Input Output :=
  .fork (.comp (.atom .fst) DFTModelOuterTailCRT.gather) (.atom .id)
def input (V : ℕ) (a : Tape ℕ) (z roles : Tape Datum.T) (k : Tape ℂ) : Input.T :=
  ((V,(a,z)),(roles,k))

attribute [local irreducible] DFTModelOuterTailCRT.gather
theorem program_run (V : ℕ) (a : Tape ℕ) (z roles : Tape Datum.T) (k : Tape ℂ) :
    run program (input V a z roles k)=
      ((run DFTModelOuterTailCRT.gather (V,(a,z))).pass
        (fun t => Bill.one (t,input V a z roles k))).pay 3 0 := by
  simp only [program,input,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,
    zero_max,max_zero,true_and,and_true]
  congr 1
  omega

theorem program_value (V : ℕ) (a : Tape ℕ) (z roles : Tape Datum.T) (k : Tape ℂ) :
    (run program (input V a z roles k)).val=
      (DFTModelOuterTailCRT.gatherValue V a z,input V a z roles k) := by
  rw [program_run]
  simp only [Bill.pass,Bill.pay,Bill.one]
  rw [DFTModelOuterTailCRT.gather_value]
  rfl

theorem program_work (V : ℕ) (a : Tape ℕ) (z roles : Tape Datum.T) (k : Tape ℂ) :
    (run program (input V a z roles k)).work=21*V+8 := by
  rw [program_run]
  simp only [Bill.pass,Bill.pay,Bill.one]
  rw [DFTModelOuterTailCRT.gather_work]

theorem program_peak (V : ℕ) (a : Tape ℕ) (z roles : Tape Datum.T) (k : Tape ℂ) :
    (run program (input V a z roles k)).peak=V := by
  rw [program_run]
  simp only [Bill.pass,Bill.pay,Bill.one]
  rw [DFTModelOuterTailCRT.gather_peak]
  omega

theorem program_valid (V : ℕ) (a : Tape ℕ) (z roles : Tape Datum.T) (k : Tape ℂ) :
    (run program (input V a z roles k)).valid := by
  rw [program_run]
  exact ⟨DFTModelOuterTailCRT.gather_valid _ _ _,trivial⟩

theorem work_preserved (V : ℕ) (a : Tape ℕ) (z roles : Tape Datum.T) (k : Tape ℂ) :
    (run program (input V a z roles k)).work≤3*(9*V+10) := by
  rw [program_work]
  omega

end
end ExactFourierCircuits.DFTModelOuterAlpha

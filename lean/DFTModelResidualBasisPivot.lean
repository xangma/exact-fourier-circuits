import DFTModelResidualBasisMask

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelResidualBasisPivot
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
noncomputable section
abbrev Input := DFTModelResidualBasisMask.Input
abbrev BodyInput := p Input (p w w)
def old : Prog false BodyInput w := .comp (.atom .snd) (.atom .snd)
def index : Prog false BodyInput w := .comp (.atom .snd) (.atom .fst)
def width : Prog false BodyInput w := .comp (.atom .fst) (.atom .fst)
def bit : Prog false BodyInput w := .comp (.fork
  (.comp (.atom .fst) (.atom .snd)) index) (.atom .look)
def choose : Prog false BodyInput w := .ifz (binary .lt old width) index old
def body : Prog false BodyInput w := .ifz bit old choose
def program : Prog false Input w := .loop (.atom .fst) (.atom .fst) body

theorem body_value (m : ℕ) (v : Tape ℕ) (i a : ℕ) :
    (run body ((m,v),(i,a))).val=if v.look i 0=0 then a else if a < m then a else i := by
  by_cases zero:v.look i 0=0 <;> by_cases low:a < m <;>
    simp [body,bit,choose,index,old,width,binary,run,Code.run,Atom.run,NOp.run,
      Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank,zero,low]

theorem body_work (m : ℕ) (v : Tape ℕ) (i a : ℕ) :
    (run body ((m,v),(i,a))).work≤23 := by
  by_cases zero:v.look i 0=0 <;> by_cases low:a < m <;>
    simp [body,bit,choose,index,old,width,binary,run,Code.run,Atom.run,NOp.run,
      Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank,zero,low]

theorem body_peak (m : ℕ) (v : Tape ℕ) (i a : ℕ) :
    (run body ((m,v),(i,a))).peak≤1 := by
  by_cases zero:v.look i 0=0 <;> by_cases low:a < m <;>
    simp [body,bit,choose,index,old,width,binary,run,Code.run,Atom.run,NOp.run,
      Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank,zero,low]

theorem body_valid (m : ℕ) (v : Tape ℕ) (i a : ℕ) : (run body ((m,v),(i,a))).valid := by
  by_cases zero:v.look i 0=0 <;> by_cases low:a < m <;>
    simp [body,bit,choose,index,old,width,binary,run,Code.run,Atom.run,NOp.run,
      Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank,zero,low]

def steps (m : ℕ) (v : Tape ℕ) (h : ℕ) : Bill ℕ :=
  Bill.steps m (fun i a=>run body ((m,v),(i,a))) h

theorem steps_value (m : ℕ) (v : Tape ℕ) (p : ℕ) (hp : p < m)
    (point : v.look p 0=1) (before : ∀i,i < p →v.look i 0=0) (h : ℕ) :
    (steps m v h).val=if h≤p then m else p := by
  induction h with
  | zero => simp [steps,Bill.steps,Bill.one]
  | succ h ih =>
    change (run body ((m,v),(h,(steps m v h).val))).val=_
    rw [body_value,ih]
    rcases lt_trichotomy h p with low|eq|high
    · have b:=before h low
      simp [b,show h≤p by omega,show h+1≤p by omega]
    · subst h
      simp [point]
    · by_cases zero:v.look h 0=0 <;>
        simp [zero,hp,show ¬h≤p by omega,show ¬h+1≤p by omega]

theorem steps_work (m : ℕ) (v : Tape ℕ) (h : ℕ) : (steps m v h).work≤24*h+1 := by
  induction h with
  | zero => change 1≤1;omega
  | succ h ih =>
    change (steps m v h).work+(run body ((m,v),(h,(steps m v h).val))).work+1≤_
    have b:=body_work m v h (steps m v h).val
    omega

theorem steps_peak (m : ℕ) (v : Tape ℕ) (h : ℕ) : (steps m v h).peak≤h+1 := by
  induction h with
  | zero => change 0≤1;omega
  | succ h ih =>
    change max (max (steps m v h).peak (run body ((m,v),(h,(steps m v h).val))).peak) (h+1)≤_
    have b:=body_peak m v h (steps m v h).val
    omega

theorem steps_valid (m : ℕ) (v : Tape ℕ) (h : ℕ) : (steps m v h).valid := by
  induction h with
  | zero => trivial
  | succ h ih => exact ⟨ih,body_valid m v h _⟩

theorem program_value (m : ℕ) (v : Tape ℕ) (p : ℕ) (hp : p < m)
    (point : v.look p 0=1) (before : ∀i,i < p →v.look i 0=0) :
    (run program (m,v)).val=p := by
  change (steps m v m).val=p
  rw [steps_value m v p hp point before]
  simp [show ¬m≤p by omega]

theorem program_work (m : ℕ) (v : Tape ℕ) : (run program (m,v)).work ≤ 24*m+4 := by
  have h:=steps_work m v m
  change 1+(1+(steps m v m).work)+1≤_
  omega

theorem program_peak (m : ℕ) (v : Tape ℕ) : (run program (m,v)).peak ≤ m+1 := by
  have h:=steps_peak m v m
  change max (max 0 (max 0 (steps m v m).peak)) 0≤_
  omega

theorem program_valid (m : ℕ) (v : Tape ℕ) : (run program (m,v)).valid := by
  change True ∧ True ∧ (steps m v m).valid
  exact ⟨trivial,trivial,steps_valid m v m⟩

/-- First nonzero direction bit is discovered by the actual loop. -/
theorem program_finds (m : ℕ) (v : Tape ℕ) (binary : ∀i,i < m →v.look i 0<2)
    (nonzero : ∃p,p < m ∧ v.look p 0=1) :
    ∃p,p < m ∧ v.look p 0=1 ∧ (∀i,i < p →v.look i 0=0) ∧ (run program (m,v)).val=p := by
  let p:=Nat.find nonzero
  have hp:=Nat.find_spec nonzero
  have before : ∀i,i < p →v.look i 0=0 := by
    intro i hi
    have b:=binary i (hi.trans hp.1)
    have no:=Nat.find_min nonzero hi
    omega
  exact ⟨p,hp.1,hp.2,before,program_value m v p hp.1 hp.2 before⟩

end
end ExactFourierCircuits.DFTModelResidualBasisPivot

import DFTModelResidualCore
import UniformResidualOrientationBridge

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualOrientation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
open scoped BigOperators
noncomputable section

abbrev Bits := p w (Ty.a w)
abbrev Input := p Bits w
abbrev Body := p Bits (p w w)
def bit : Prog false Body w := .comp (.fork
  (.comp (.atom .fst) (.atom .snd)) (.comp (.atom .snd) (.atom .fst))) (.atom .look)
def body : Prog false Body w := binary .mod
  (binary .add (.comp (.atom .snd) (.atom .snd)) bit) (.atom (.lit 4))
def scan : Prog false Bits w := .loop (.atom .fst) (.atom (.lit 0)) body
def choice : Prog false (p w w) w := .ifz
  (binary .lt (.atom .fst) (.atom (.lit 3)))
  (binary .mod (binary .add (.atom .snd) (.atom (.lit 1))) (.atom (.lit 2)))
  (.atom .snd)
def program : Prog false Input w := .comp
  (.fork (.comp (.atom .fst) scan) (.atom .snd)) choice

def residue (raw:Tape ℕ) (i:ℕ) : ℕ := (∑j∈Finset.range i,raw.look j 0)%4
def steps (m:ℕ) (raw:Tape ℕ) (i:ℕ) : Bill ℕ :=
  Bill.steps 0 (fun j z=>run body ((m,raw),(j,z))) i

theorem body_run (m:ℕ) (raw:Tape ℕ) (i z:ℕ) :
  run body ((m,raw),(i,z))=⟨(z+raw.look i 0)%4,19,
    max 4 (z+raw.look i 0),True⟩ := by
  simp [body,bit,binary,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank,max_comm,max_left_comm]
  have small:=Nat.mod_lt (z+raw.look i 0) (show 0<4 by decide)
  omega

theorem residue_succ (raw:Tape ℕ) (i:ℕ) :
  residue raw (i+1)=(residue raw i+raw.look i 0)%4 := by
  simp [residue,Finset.sum_range_succ,Nat.add_mod]

theorem steps_value (m:ℕ) (raw:Tape ℕ) (i:ℕ) : (steps m raw i).val=residue raw i := by
  induction i with
  | zero=>simp [steps,Bill.steps,Bill.one,residue]
  | succ i ih=>change (run body ((m,raw),(i,(steps m raw i).val))).val=_
               rw [ih,body_run,residue_succ]

theorem steps_work (m:ℕ) (raw:Tape ℕ) (i:ℕ) : (steps m raw i).work=20*i+1 := by
  induction i with
  | zero=>rfl
  | succ i ih=>change (steps m raw i).work+(run body ((m,raw),(i,(steps m raw i).val))).work+1=_
               rw [ih,body_run];dsimp only [Bill.work];omega

theorem steps_valid (m:ℕ) (raw:Tape ℕ) (i:ℕ) : (steps m raw i).valid := by
  induction i with
  | zero=>trivial
  | succ i ih=>change (steps m raw i).valid ∧ (run body ((m,raw),(i,(steps m raw i).val))).valid
               rw [body_run];exact ⟨ih,trivial⟩

theorem scan_value (m:ℕ) (raw:Tape ℕ) : (run scan (m,raw)).val=residue raw m := by
  change (steps m raw m).val=_;exact steps_value _ _ _
theorem scan_work (m:ℕ) (raw:Tape ℕ) : (run scan (m,raw)).work=20*m+4 := by
  change 1+(1+(steps m raw m).work)+1=_;rw [steps_work];omega
theorem scan_valid (m:ℕ) (raw:Tape ℕ) : (run scan (m,raw)).valid := by
  exact ⟨trivial,trivial,steps_valid _ _ _⟩

theorem choice_run (weight raw:ℕ) (hw:weight<4) :
  run choice (weight,raw)=⟨UniformResidualOrientationMachine.effective raw weight,
    if weight=3 then 15 else 7,max 3 (if weight=3 then max 2 (raw+1) else 0),True⟩ := by
  by_cases h:weight=3
  · subst weight
    simp [choice,binary,run,Code.run,Atom.run,NOp.run,
      Bill.pass,Bill.pay,Bill.one,Bill.word,UniformResidualOrientationMachine.effective]
    have md:=Nat.mod_lt (raw+1) (show 0<2 by decide)
    omega
  · have lt:weight<3:=by omega
    simp [choice,binary,run,Code.run,Atom.run,NOp.run,
      Bill.pass,Bill.pay,Bill.one,Bill.word,UniformResidualOrientationMachine.effective,h,lt]

theorem program_value (m:ℕ) (bits:Tape ℕ) (raw:ℕ) :
  (run program ((m,bits),raw)).val=
    UniformResidualOrientationMachine.effective raw (residue bits m) := by
  have small:residue bits m<4:=Nat.mod_lt _ (by decide)
  change (run choice ((run scan (m,bits)).val,raw)).val=_
  rw [scan_value,choice_run _ _ small]

theorem program_work (m:ℕ) (bits:Tape ℕ) (raw:ℕ) :
  (run program ((m,bits),raw)).work≤20*m+25 := by
  have small:residue bits m<4:=Nat.mod_lt _ (by decide)
  change (1+(run scan (m,bits)).work+1)+1+1+
    (run choice ((run scan (m,bits)).val,raw)).work+1≤_
  rw [scan_value,scan_work,choice_run _ _ small]
  dsimp only [Bill.work];split <;>omega

theorem program_valid (m:ℕ) (bits:Tape ℕ) (raw:ℕ) :
  (run program ((m,bits),raw)).valid := by
  have small:residue bits m<4:=Nat.mod_lt _ (by decide)
  have good:=scan_valid m bits
  have last:(run choice ((run scan (m,bits)).val,raw)).valid:=by
    rw [scan_value,choice_run _ _ small];trivial
  simpa only [program,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,
    and_true,true_and] using And.intro good last

theorem source_value {m:ℕ} (v:BinaryFrames.Vec (Fin m)) (bits:Tape ℕ)
  (source:∀i:Fin m,bits.look i.val 0=(v i).val) (hv:BinaryFrames.dot v v=1) (inverse:Bool) :
  (run program ((m,bits),UniformResidualOrientationArithmetic.boolCode inverse)).val=
    UniformResidualOrientationArithmetic.boolCode (UniformResidualFibers.inverseOrientation v inverse) := by
  rw [program_value]
  have e:residue bits m=UniformResidualOrientationMachine.residue v m := by
    unfold residue UniformResidualOrientationMachine.residue
    congr 1
    rw [←Fin.sum_univ_eq_sum_range (fun i=>bits.look i 0) m,
      ←Fin.sum_univ_eq_sum_range (UniformRepeatedMaskMachine.bits v) m]
    apply Finset.sum_congr rfl
    intro i _
    rw [source i]
    simp [UniformRepeatedMaskMachine.bits]
  rw [e]
  exact UniformResidualOrientationBridge.effective_orientation v hv inverse

end
end ExactFourierCircuits.DFTModelSavingResidualOrientation

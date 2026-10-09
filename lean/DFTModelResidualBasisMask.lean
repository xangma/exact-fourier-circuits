import DFTModelResidualCore
import UniformResidualPermutation

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelResidualBasisMask
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
open scoped BigOperators
noncomputable section

abbrev Input := p w (Ty.a w)
abbrev Acc := p w w
abbrev BodyInput := p Input (p w Acc)
def old : Prog false BodyInput Acc := .comp (.atom .snd) (.atom .snd)
def place : Prog false BodyInput w := .comp old (.atom .fst)
def accumulated : Prog false BodyInput w := .comp old (.atom .snd)
def bit : Prog false BodyInput w := .comp (.fork
  (.comp (.atom .fst) (.atom .snd)) (.comp (.atom .snd) (.atom .fst))) (.atom .look)
def body : Prog false BodyInput Acc := .fork
  (binary .mul place (.atom (.lit 2)))
  (binary .add accumulated (binary .mul place bit))
def initial : Prog false Input Acc := .fork (.atom (.lit 1)) (.atom (.lit 0))
def loop : Prog false Input Acc := .loop (.atom .fst) initial body
def program : Prog false Input w := .comp loop (.atom .snd)

def maskPrefix (v : Tape ℕ) (h : ℕ) : ℕ := ∑i∈Finset.range h,2^i*v.look i 0

theorem maskPrefix_succ (v : Tape ℕ) (h : ℕ) :
    maskPrefix v (h+1)=maskPrefix v h+2^h*v.look h 0 := by
  simp [maskPrefix,Finset.sum_range_succ]

theorem body_run (m : ℕ) (v : Tape ℕ) (i p c : ℕ) :
    run body ((m,v),(i,(p,c)))=
      ⟨(p*2,c+p*v.look i 0),35,max 2 (max (p*2) (max (p*v.look i 0) (c+p*v.look i 0))),True⟩ := by
  simp [body,place,accumulated,bit,old,binary,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank,max_assoc]

def steps (m : ℕ) (v : Tape ℕ) (h : ℕ) : Bill Acc.T :=
  Bill.steps (1,0) (fun i z=>run body ((m,v),(i,z))) h

theorem steps_value (m : ℕ) (v : Tape ℕ) (h : ℕ) :
    (steps m v h).val=(2^h,maskPrefix v h) := by
  induction h with
  | zero => simp [steps,Bill.steps,Bill.one,maskPrefix]
  | succ h ih =>
    change (run body ((m,v),(h,(steps m v h).val))).val=_
    rw [ih,body_run]
    simp only [maskPrefix,Finset.sum_range_succ,Nat.pow_succ]

theorem steps_work (m : ℕ) (v : Tape ℕ) (h : ℕ) :
    (steps m v h).work=36*h+1 := by
  induction h with
  | zero => rfl
  | succ h ih =>
    change (steps m v h).work+(run body ((m,v),(h,(steps m v h).val))).work+1=_
    rw [steps_value,body_run,ih]
    dsimp only [Bill.work]
    omega

theorem steps_valid (m : ℕ) (v : Tape ℕ) (h : ℕ) : (steps m v h).valid := by
  induction h with
  | zero => trivial
  | succ h ih =>
    change (steps m v h).valid ∧ (run body ((m,v),(h,(steps m v h).val))).valid
    rw [steps_value,body_run]
    exact ⟨ih,trivial⟩

theorem maskPrefix_lt (m : ℕ) (v : Tape ℕ) (binary : ∀i,i < m →v.look i 0<2)
    (h : ℕ) (hm : h ≤ m) : maskPrefix v h<2^h := by
  induction h with
  | zero => simp [maskPrefix]
  | succ h ih =>
    have old:=ih (by omega)
    have digit:=binary h (by omega)
    have prod:=Nat.mul_le_mul_left (2^h) (show v.look h 0≤1 by omega)
    simp only [Nat.mul_one] at prod
    simp only [maskPrefix,Finset.sum_range_succ,Nat.pow_succ] at old ⊢
    omega

theorem program_value (m : ℕ) (v : Tape ℕ) :
    (run program (m,v)).val=maskPrefix v m := by
  change (steps m v m).val.2=_
  rw [steps_value]

theorem program_work (m : ℕ) (v : Tape ℕ) : (run program (m,v)).work=36*m+8 := by
  change (1+(3+(steps m v m).work)+1)+1+1=_
  rw [steps_work]
  omega

theorem program_valid (m : ℕ) (v : Tape ℕ) : (run program (m,v)).valid := by
  simpa only [program,loop,initial,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,
    Bill.word,steps,and_true,true_and] using steps_valid m v m

theorem steps_peak (m : ℕ) (v : Tape ℕ) (binary : ∀i,i < m →v.look i 0<2)
    (h : ℕ) (hm : h ≤ m) : (steps m v h).peak≤2^h+2 := by
  induction h with
  | zero => change 0≤_;omega
  | succ h ih =>
    have prior:=ih (by omega)
    have value:=steps_value m v h
    have digit:=binary h (by omega)
    have prod:=Nat.mul_le_mul_left (2^h) (show v.look h 0≤1 by omega)
    simp only [Nat.mul_one] at prod
    have part:=maskPrefix_lt m v binary (h+1) hm
    have idx: h+1≤2^(h+1)+2 := (h+1).lt_two_pow_self.le.trans (by omega)
    change max (max (steps m v h).peak (run body ((m,v),(h,(steps m v h).val))).peak) (h+1)≤_
    rw [value,body_run]
    dsimp only [Bill.peak]
    rw [Nat.pow_succ]
    rw [maskPrefix_succ] at part
    rw [Nat.pow_succ] at part idx
    simp only [max_le_iff]
    repeat' apply And.intro
    all_goals omega

theorem program_peak (m : ℕ) (v : Tape ℕ) (binary : ∀i,i < m →v.look i 0<2) :
    (run program (m,v)).peak≤2^m+2 := by
  have h:=steps_peak m v binary m le_rfl
  have positive:=Nat.two_pow_pos m
  change max (max (max (max 0 (max (max 1 (max 0 0)) (steps m v m).peak)) 0) 0) 0≤_
  simp only [max_le_iff]
  repeat' apply And.intro
  all_goals omega

/-- The encoded mask comes from the actual original direction cells. -/
theorem source_value (m : ℕ) (v : BinaryFrames.Vec (Fin m)) (data : Tape ℕ)
    (source : ∀i:Fin m,data.look i.val 0=(v i).val) :
    (run program (m,data)).val=(UniformBinaryXorCoordinates.encode v).val := by
  rw [program_value,UniformBinaryXorCoordinates.encode_value]
  unfold maskPrefix
  rw [←Fin.sum_univ_eq_sum_range (fun i=>2^i*data.look i 0) m]
  apply Finset.sum_congr rfl
  intro i _
  rw [source i]

end
end ExactFourierCircuits.DFTModelResidualBasisMask

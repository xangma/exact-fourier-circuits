import DFTModelMemoryAffinePointwise
import UniformBlockXorMachine

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelResidualCore
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

def binary {s : Ty} (op : NOp) (f g : Prog false s w) : Prog false s w :=
  .comp (.fork f g) (.atom (.int op))

theorem binary_work {s : Ty} (op : NOp) (f g : Prog false s w) (x : s.T) :
    (run (binary op f g) x).work = (run f x).work+(run g x).work+3 := by
  cases op <;> simp [binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Nat.add_assoc]

theorem binary_valid {s : Ty} (op : NOp) (f g : Prog false s w) (x : s.T) :
    (run (binary op f g) x).valid ↔ (run f x).valid ∧ (run g x).valid := by
  cases op <;> simp [binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

def powerBody : Prog false (p w (p w w)) w :=
  binary .mul (.comp (.atom .snd) (.atom .snd)) (.atom (.lit 2))
def power : Prog false w w := .loop (.atom .id) (.atom (.lit 1)) powerBody

theorem powerBody_run (q i a : ℕ) :
    run powerBody (q,(i,a)) = ⟨a*2,7,max 2 (a*2),True⟩ := by
  simp [powerBody,binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

def powerSteps (q : ℕ) : Bill ℕ := Bill.steps 1
  (fun i a => run powerBody (q,(i,a))) q

theorem powerSteps_value (q : ℕ) : (powerSteps q).val = 2^q := by
  suffices h : ∀j, (Bill.steps 1 (fun i a => run powerBody (q,(i,a))) j).val=2^j from h q
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    change (run powerBody (q,(j,(Bill.steps 1 (fun i a => run powerBody (q,(i,a))) j).val))).val = _
    rw [powerBody_run,ih,Nat.pow_succ]

theorem powerSteps_work (q : ℕ) : (powerSteps q).work = 8*q+1 := by
  suffices h : ∀j, (Bill.steps 1 (fun i a => run powerBody (q,(i,a))) j).work=8*j+1 from h q
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    change (Bill.steps 1 (fun i a => run powerBody (q,(i,a))) j).work+
      (run powerBody (q,(j,(Bill.steps 1 (fun i a => run powerBody (q,(i,a))) j).val))).work+1 = _
    rw [powerBody_run,ih]
    dsimp only [Bill.work]
    omega

theorem powerSteps_valid (q : ℕ) : (powerSteps q).valid := by
  suffices h : ∀j, (Bill.steps 1 (fun i a => run powerBody (q,(i,a))) j).valid from h q
  intro j
  induction j with
  | zero => trivial
  | succ j ih =>
    change ((Bill.steps 1 (fun i a => run powerBody (q,(i,a))) j).valid ∧
      (run powerBody (q,(j,(Bill.steps 1 (fun i a => run powerBody (q,(i,a))) j).val))).valid)
    rw [powerBody_run]
    exact ⟨ih,trivial⟩

theorem powerSteps_general_value (q j : ℕ) :
    (Bill.steps 1 (fun i a => run powerBody (q,(i,a))) j).val=2^j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (run powerBody (q,(j,(Bill.steps 1 (fun i a => run powerBody (q,(i,a))) j).val))).val = _
    rw [powerBody_run,ih,Nat.pow_succ]

theorem powerSteps_peak (q : ℕ) : (powerSteps q).peak≤2^q := by
  suffices h : ∀j,(Bill.steps 1 (fun i a=>run powerBody (q,(i,a))) j).peak≤2^j from h q
  intro j
  induction j with
  | zero => change 0≤1;omega
  | succ j ih =>
    change max (max (Bill.steps 1 (fun i a=>run powerBody (q,(i,a))) j).peak
      (run powerBody (q,(j,(Bill.steps 1 (fun i a=>run powerBody (q,(i,a))) j).val))).peak) (j+1)≤_
    rw [powerBody_run,powerSteps_general_value]
    have pos:=Nat.two_pow_pos j
    have jb: j+1≤2^(j+1):=Nat.le_of_lt (j+1).lt_two_pow_self
    rw [Nat.pow_succ] at jb ⊢
    dsimp only [Bill.peak]
    omega

theorem power_peak (q : ℕ) : (run power q).peak≤2^q := by
  change max (max 0 (max 1 (powerSteps q).peak)) 0≤_
  have h:=powerSteps_peak q
  have pos:=Nat.two_pow_pos q
  omega

theorem power_value (q : ℕ) : (run power q).val = 2^q := powerSteps_value q

theorem power_work (q : ℕ) : (run power q).work = 8*q+4 := by
  change 1+(1+(powerSteps q).work)+1 = _
  rw [powerSteps_work]
  omega

theorem power_valid (q : ℕ) : (run power q).valid := by
  change True ∧ True ∧ (powerSteps q).valid
  exact ⟨trivial,trivial,powerSteps_valid q⟩

end
end ExactFourierCircuits.DFTModelResidualCore

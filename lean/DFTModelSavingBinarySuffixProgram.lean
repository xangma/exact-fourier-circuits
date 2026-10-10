import DFTModelSavingBinaryCost

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingBinarySuffix
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelRecursiveScalarCore
noncomputable section

abbrev Input := p w DFTModelClockControl.Node
abbrev PowerIter := p Input (p w w)
abbrev Iter := p Input (p w DFTModelRecursiveBinary.Acc)

def powerBody : Prog false PowerIter w :=
  .comp (.fork (.comp (.atom .snd) (.atom .snd)) (.atom (.lit 2))) (.atom (.int .mul))
def power : Prog false Input w := .loop (.atom .fst) (.atom (.lit 1)) powerBody

def start : Prog false Input DFTModelRecursiveBinary.Acc :=
  .fork power (.comp (.atom .snd) (.atom .snd))
def count : Prog false Input w :=
  .comp (.fork (.comp (.atom .snd) DFTModelRecursiveBinary.bits) (.atom .fst)) (.atom (.int .sub))
def body : Prog false Iter DFTModelRecursiveBinary.Acc :=
  .comp (.fork (.comp (.atom .fst) (.atom .snd)) (.atom .snd)) DFTModelRecursiveBinary.body

def loop : Prog false Input DFTModelRecursiveBinary.Acc := .loop count start body
def tapeProgram : Prog false Input (Ty.a Tagged) := .comp loop (.atom .snd)
def program : Prog false Input DFTModelClockControl.Node :=
  .fork (.comp (.atom .snd) (.atom .fst)) tapeProgram

attribute [local irreducible] DFTModelRecursiveBinary.body body powerBody program

theorem typed_loop_run {s t : Ty} (n : Prog false s w) (initial : Prog false s t)
    (f : Prog false (p s (p w t)) t) (x : s.T) :
    run (.loop n initial f) x=((run n x).pass (fun l => (run initial x).pass
      (fun z => Bill.steps z (fun i a => run f (x,(i,a))) l))).pay 1 0 := rfl

def powerSteps (x : Input.T) (j : ℕ) : Bill ℕ := Bill.steps 1 (fun i P => run powerBody (x,(i,P))) j

theorem powerBody_run (x : Input.T) (i P : ℕ) :
    run powerBody (x,(i,P))=⟨2*P,7,max 2 (2*P),True⟩ := by
  simp [powerBody,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Nat.mul_comm]

theorem powerSteps_value (x : Input.T) (j : ℕ) : (powerSteps x j).val=2^j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (run powerBody (x,(j,(powerSteps x j).val))).val=_
    rw [ih,powerBody_run,Nat.pow_succ]
    change 2*2^j=2^j*2
    exact Nat.mul_comm _ _

theorem powerSteps_work (x : Input.T) (j : ℕ) : (powerSteps x j).work=1+8*j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (powerSteps x j).work+(run powerBody (x,(j,(powerSteps x j).val))).work+1=_
    rw [powerBody_run,ih]
    change 1+8*j+7+1=_
    omega

theorem powerSteps_valid (x : Input.T) (j : ℕ) : (powerSteps x j).valid := by
  induction j with
  | zero => trivial
  | succ j ih =>
    change (powerSteps x j).valid ∧ (run powerBody (x,(j,(powerSteps x j).val))).valid
    rw [powerBody_run]
    exact ⟨ih,trivial⟩

theorem powerSteps_peak (x : Input.T) (j : ℕ) : (powerSteps x j).peak≤2^j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    have hp : 1≤2^j := Nat.one_le_pow j 2 (by omega)
    have hj : j+1≤2^(j+1) := DFTModelSavingBinary.bits_le_volume (j+1)
    change max (max (powerSteps x j).peak
      (run powerBody (x,(j,(powerSteps x j).val))).peak) (j+1)≤_
    rw [powerSteps_value,powerBody_run,Nat.pow_succ] at *
    change max (max (powerSteps x j).peak (max 2 (2*2^j))) (j+1)≤_
    omega

theorem power_run (b : ℕ) (node : DFTModelClockControl.Node.T) :
    run power (b,node)=(powerSteps (b,node) b).pay 3 1 := by
  rw [power,typed_loop_run]
  simp only [atom_run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay,true_and,zero_max,max_zero]
  congr 1
  · change 1+(1+(powerSteps (b,node) b).work)+1=(powerSteps (b,node) b).work+3
    omega
  · exact max_comm _ _

theorem power_value (b : ℕ) (node : DFTModelClockControl.Node.T) :
    (run power (b,node)).val=2^b := by rw [power_run];exact powerSteps_value _ _
theorem power_work (b : ℕ) (node : DFTModelClockControl.Node.T) :
    (run power (b,node)).work=4+8*b := by
  rw [power_run]
  change (powerSteps (b,node) b).work+3=_
  rw [powerSteps_work];omega
theorem power_valid (b : ℕ) (node : DFTModelClockControl.Node.T) : (run power (b,node)).valid := by
  rw [power_run];exact powerSteps_valid _ _
theorem power_peak (b : ℕ) (node : DFTModelClockControl.Node.T) : (run power (b,node)).peak≤2^b := by
  rw [power_run]
  exact max_le (powerSteps_peak _ _) (Nat.one_le_pow _ _ (by omega))

theorem count_run (b k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    run count (b,((k,I),v))=⟨k-b,9,k-b,True⟩ := by
  simp only [count,comp_run,fork_run,atom_run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  rw [DFTModelRecursiveBinary.bits_run]
  simp [NOp.run,Bill.word]

theorem start_run (b k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    run start (b,((k,I),v))=⟨(2^b,v),8+8*b,(run power (b,((k,I),v))).peak,True⟩ := by
  simp only [start,fork_run,comp_run,atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  rw [power_value,power_work]
  simp only [max_zero,and_true]
  congr 1
  · omega
  · exact propext (iff_true_intro (power_valid _ _))

theorem body_run (b k i P : ℕ) (I : ℂ) (old v : Tape Tagged.T) :
    run body ((b,((k,I),old)),(i,(P,v)))=
      (run DFTModelRecursiveBinary.body (((k,I),old),(i,(P,v)))).pay 6 0 := by
  simp only [body,comp_run,fork_run,atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay,max_zero,true_and]
  congr 1
  omega

end
end ExactFourierCircuits.DFTModelSavingBinarySuffix

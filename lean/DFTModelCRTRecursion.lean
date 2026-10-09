import DFTModelCRTProgram

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCRT
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

def prefixTable : ℕ → Args.T → Tape (ℕ × ℕ)
  | 0, _ => Tape.tab 1 (fun _ => (0,0))
  | k+1, x => enlarged x (prefixTable k (successor x))

def volumeSum : ℕ → Args.T → ℕ
  | 0, _ => 0
  | k+1, x => volumeSum k (successor x)+(prefixTable (k+1) x).len

theorem base_valid (x : Args.T) : (run base x).valid := by
  simp [base,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word,
    Bill.tab,Bill.sow,Bill.steps,Ty.blank]

theorem step_run (h : Args.T → Bill (Tape (ℕ × ℕ))) (x : Args.T) :
    Code.run step h x =
      let child := h (successor x)
      let e := run extend (x,child.val)
      ⟨e.val,child.work+e.work+14,
        max (x.1+1) (max child.peak e.peak),child.valid ∧ e.valid⟩ := by
  simp [step,run,Code.run,next_run,Atom.run,Bill.pass,Bill.pay,Bill.one,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,max_assoc]
  omega

theorem depth_value (k : ℕ) (x : Args.T) :
    (depthRun (run base) (Code.run step) k x).val = prefixTable k x := by
  induction k generalizing x with
  | zero => exact base_value x
  | succ k ih =>
      simp only [depthRun,step_run,Bill.pay,prefixTable]
      rw [extend_value,ih]

theorem depth_work (k : ℕ) (x : Args.T) :
    (depthRun (run base) (Code.run step) k x).work =
      12+119*volumeSum k x+35*k := by
  induction k generalizing x with
  | zero => simp [depthRun,base_work,Bill.pay,volumeSum]
  | succ k ih =>
      simp only [depthRun,step_run,Bill.pay]
      rw [extend_work,depth_value,ih]
      change _ = 12+119*(volumeSum k (successor x)+
        (readRow x).1*(prefixTable k (successor x)).len)+35*(k+1)
      omega

theorem depth_valid (k : ℕ) (x : Args.T) :
    (depthRun (run base) (Code.run step) k x).valid := by
  induction k generalizing x with
  | zero => exact base_valid x
  | succ k ih =>
      simp only [depthRun,step_run,Bill.pay]
      exact ⟨ih _,extend_valid _ _⟩

theorem tables_value (k : ℕ) (x : Args.T) :
    (run tables (k,x)).val = prefixTable k x := depth_value k x

theorem tables_work (k : ℕ) (x : Args.T) :
    (run tables (k,x)).work = 13+119*volumeSum k x+35*k := by
  change (depthRun (run base) (Code.run step) k x).work+1 = _
  rw [depth_work]
  omega

theorem tables_valid (k : ℕ) (x : Args.T) : (run tables (k,x)).valid :=
  depth_valid k x

end
end ExactFourierCircuits.DFTModelCRT

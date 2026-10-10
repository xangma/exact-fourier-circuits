import DFTModelSavingNativePaddingLoopResult
import DFTModelSavingCostPadding
import DFTModelSavingCostDispatch

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSavingNativePaddingLoop
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl
noncomputable section
attribute [local irreducible] DFTModelCacheRecords.unit DFTModelSavingRecords.residual
  DFTModelSavingCost.unitAllowance DFTModelCacheRecords.recordCost UniformRecursiveSavingProgram.unitRecord

lemma steps_shift_work {α : Type} (x : α) (f : ℕ→α→Bill α) (n : ℕ) :
    (Bill.steps x f (n+1)).work=(f 0 x).work+
      (Bill.steps (f 0 x).val (fun i=>f (i+1)) n).work+1 := by
  induction n with
  | zero=>simp [Bill.steps,Bill.one,Bill.pass,Bill.pay,Nat.add_comm]
  | succ n ih=>
    change (Bill.steps x f (n+1)).work+
      (f (n+1) (Bill.steps x f (n+1)).val).work+1=_
    rw [ih,DFTModelSavingChronology.steps_succ_start]
    change _=(f 0 x).work+
      ((Bill.steps (f 0 x).val (fun i=>f (i+1)) n).work+
        (f (n+1) (Bill.steps (f 0 x).val (fun i=>f (i+1)) n).val).work+1)+1
    omega

lemma fold_work_succ (h : Handler DFTModelSavingRecords.Port) (q rest index count : ℕ)
    (node : Node.T) :
    (DFTModelSavingNativePaddingFold.steps h q rest index (count+1) node).work=
      (DFTModelSavingNativePaddingFold.role h q rest index node).work+
      (DFTModelSavingNativePaddingFold.steps h q rest (index+1) count
        (DFTModelSavingNativePaddingFold.role h q rest index node).val).work+1 := by
  unfold DFTModelSavingNativePaddingFold.steps
  rw [steps_shift_work]
  simp only [Nat.add_zero,Nat.add_assoc,Nat.add_comm 1]

lemma padding_prefix_value (h : Handler DFTModelSavingRecords.Port)
    (q rest start count : ℕ) (raw : Tape ℕ) (node : Node.T)
    (columns : raw.look 1 0=q) (first : raw.look 3 0=start) :
    (DFTModelSavingPadding.steps h rest raw node count).val=
      (DFTModelSavingNativePaddingFold.steps h q rest start count node).val := by
  unfold DFTModelSavingPadding.steps DFTModelSavingNativePaddingFold.steps
  apply DFTModelSavingRecords.steps_value_congr
  intro i current
  exact DFTModelSavingNativePaddingValue.role_value h q start rest i raw node current columns first

lemma steps_work_le {α : Type} (x : α) (f g : ℕ→α→Bill α) (count C : ℕ)
    (value : ∀i current,(f i current).val=(g i current).val)
    (work : ∀i current,(f i current).work≤(g i current).work+C) :
    (Bill.steps x f count).work≤(Bill.steps x g count).work+count*C := by
  induction count with
  | zero=>simp [Bill.steps,Bill.one]
  | succ count ih=>
    have beforeVal : (Bill.steps x f count).val=(Bill.steps x g count).val :=
      DFTModelSavingRecords.steps_value_congr x f g value count
    have step:=work count (Bill.steps x f count).val
    rw [beforeVal] at step
    change (Bill.steps x f count).work+(f count (Bill.steps x f count).val).work+1≤
      (Bill.steps x g count).work+(g count (Bill.steps x g count).val).work+1+(count+1)*C
    rw [beforeVal,Nat.succ_mul]
    omega

/-- This bound pays each actual fresh unit print; no produced unit tape is an input. -/
lemma padding_prefix_work (h : Handler DFTModelSavingRecords.Port)
    (q rest start count : ℕ) (raw : Tape ℕ) (node : Node.T)
    (columns : raw.look 1 0=q) (first : raw.look 3 0=start) :
    (DFTModelSavingPadding.steps h rest raw node count).work≤
      (DFTModelSavingNativePaddingFold.steps h q rest start count node).work+
        count*(DFTModelSavingCost.unitAllowance+36) := by
  apply steps_work_le
  · intro i current
    exact DFTModelSavingNativePaddingValue.role_value h q start rest i raw node current columns first
  · intro i current
    rw [DFTModelSavingCost.padding_role_work_exact,columns,first]
    exact Nat.add_le_add_left (Nat.add_le_add_right (DFTModelSavingCost.unit_work_bound q (start+i)) 36) _

lemma dispatch_fold_work (h : Handler DFTModelSavingRecords.Port)
    (R q rest start count : ℕ) (raw : Tape ℕ) (node : Node.T)
    (opcode : raw.look 0 0=5) (columns : raw.look 1 0=q)
    (first : raw.look 3 0=start) (length : raw.look 4 0=count) :
    (Code.run (DFTModelSavingRecords.dispatch R) h (rest,(raw,node))).work+22≤
      (DFTModelSavingNativePaddingFold.steps h q rest start count node).work+
        count*(DFTModelSavingCost.unitAllowance+37)+109 := by
  rw [DFTModelSavingCost.dispatch_work,opcode]
  norm_num only [Nat.reduceSub,Nat.reduceEqDiff,ite_false,ite_true]
  rw [DFTModelSavingPadding.padding_run]
  change (DFTModelSavingPadding.steps h rest raw node (raw.look 4 0)).work+13+74+22≤_
  rw [length]
  have bound:=padding_prefix_work h q rest start count raw node columns first
  have mono:=Nat.mul_le_mul_left count (show DFTModelSavingCost.unitAllowance+36≤
    DFTModelSavingCost.unitAllowance+37 by omega)
  omega

end
end ExactFourierCircuits.DFTModelSavingNativePaddingLoop

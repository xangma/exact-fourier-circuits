import DFTModelSavingNativePaddingValue
import DFTModelSavingChronology

set_option autoImplicit false

/-! Paper E (adc7f), §2.6. The padding roles run in ascending order and
each consumes the exact bank returned by the preceding residual call. -/
namespace ExactFourierCircuits.DFTModelSavingNativePaddingFold
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelSavingRecords
noncomputable section
attribute [local irreducible] DFTModelSavingRecords.residual DFTModelCacheRecords.unit

def role (h : Handler Port) (q rest index : ℕ) (node : Node.T) : Bill Node.T :=
  Code.run DFTModelSavingRecords.residual h
    (rest,((run DFTModelCacheRecords.unit (q,index)).val,node))

def steps (h : Handler Port) (q rest index count : ℕ) (node : Node.T) : Bill Node.T :=
  Bill.steps node (fun i current=>role h q rest (index+i) current) count

theorem steps_zero (h : Handler Port) (q rest index : ℕ) (node : Node.T) :
    (steps h q rest index 0 node).val=node := rfl

theorem steps_succ (h : Handler Port) (q rest index count : ℕ) (node : Node.T) :
    (steps h q rest index (count+1) node).val=
      (steps h q rest (index+1) count (role h q rest index node).val).val := by
  unfold steps
  rw [DFTModelSavingChronology.steps_succ_start]
  simp only [Nat.add_zero,Nat.add_assoc,Nat.add_comm 1]

theorem padding_value (h : Handler Port) (rest : ℕ) (raw : Tape ℕ) (node : Node.T) :
    (Code.run DFTModelSavingRecords.padding h (rest,(raw,node))).val=
      (steps h (raw.look 1 0) rest (raw.look 3 0) (raw.look 4 0) node).val := by
  rw [DFTModelSavingPadding.padding_run]
  change (DFTModelSavingPadding.steps h rest raw node (raw.look 4 0)).val=_
  unfold DFTModelSavingPadding.steps steps
  apply DFTModelSavingRecords.steps_value_congr
  intro i current
  exact DFTModelSavingNativePaddingValue.role_value h _ _ rest i raw node current rfl rfl

end
end ExactFourierCircuits.DFTModelSavingNativePaddingFold

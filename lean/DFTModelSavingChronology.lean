import DFTModelSavingControl
import DFTModelSavingNativeControl

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingChronology
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine
open UniformFixedNetworkScheduleMachine (Record)
noncomputable section
attribute [local irreducible] DFTModelSavingRecords.dispatch DFTModelSavingRecords.stream

def recordStep (R rest : ℕ) (h : Handler ChildPort) (r : Record) (node : Node.T) : Node.T :=
  ((DFTModelSavingRecords.dispatch R).run h
    (rest,(DFTModelCacheRecords.dataTape r.data,node))).val

def recordFold (R rest : ℕ) (h : Handler ChildPort) (rs : List Record) (node : Node.T) : Node.T :=
  rs.foldl (fun current r=>recordStep R rest h r current) node

lemma steps_succ_start {α : Type} (x : α) (f : ℕ→α→Bill α) (n : ℕ) :
    (Bill.steps x f (n+1)).val=
      (Bill.steps (f 0 x).val (fun i=>f (i+1)) n).val := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    change (f (n+1) (Bill.steps x f (n+1)).val).val=
      (f (n+1) (Bill.steps (f 0 x).val (fun i=>f (i+1)) n).val).val
    rw [ih]

lemma recordTape_head (r : Record) (rs : List Record) :
    (DFTModelCacheRecords.recordTape (r::rs)).look 0 (Tape.empty ℕ)=
      DFTModelCacheRecords.dataTape r.data := by
  exact DFTModelSavingNativeControl.recordTape_lookup (r::rs) 0 (by simp)

lemma recordTape_tail (r : Record) (rs : List Record) (i : ℕ) :
    (DFTModelCacheRecords.recordTape (r::rs)).look (i+1) (Tape.empty ℕ)=
      (DFTModelCacheRecords.recordTape rs).look i (Tape.empty ℕ) := by
  by_cases hi:i<rs.length
  · rw [DFTModelSavingNativeControl.recordTape_lookup (r::rs) (i+1) (by simp;omega),
      DFTModelSavingNativeControl.recordTape_lookup rs i hi]
    rfl
  · rw [Tape.look_of_le _ _ (by change (r :: rs).length ≤ i + 1; simp; omega),
      Tape.look_of_le _ _ (by change rs.length ≤ i; omega)]

lemma stream_cons (R rest : ℕ) (h : Handler ChildPort) (r : Record) (rs : List Record) (node : Node.T) :
    ((DFTModelSavingRecords.stream R).run h
      (rest,(DFTModelCacheRecords.recordTape (r::rs),node))).val=
    ((DFTModelSavingRecords.stream R).run h
      (rest,(DFTModelCacheRecords.recordTape rs,recordStep R rest h r node))).val := by
  rw [DFTModelSavingRecords.stream_value,DFTModelSavingRecords.stream_value]
  change (Bill.steps node
    (fun i current=>(DFTModelSavingRecords.dispatch R).run h
      (rest,((DFTModelCacheRecords.recordTape (r::rs)).look i (Tape.empty ℕ),current)))
    (rs.length+1)).val=_
  rw [steps_succ_start,recordTape_head]
  apply DFTModelSavingControl.steps_value_congr_range
  intro i hi current
  rw [recordTape_tail]

/-- The concrete stream executes each actual raw record exactly in list order.
In particular successive shears consume the previously returned paired bank. -/
theorem stream_list_value (R rest : ℕ) (h : Handler ChildPort) (rs : List Record) (node : Node.T) :
    ((DFTModelSavingRecords.stream R).run h
      (rest,(DFTModelCacheRecords.recordTape rs,node))).val=recordFold R rest h rs node := by
  induction rs generalizing node with
  | nil=>rw [DFTModelSavingRecords.stream_value];rfl
  | cons r rs ih=>rw [stream_cons,ih];rfl

/-- Specialization to the runtime-produced fixed saving tape; no tape is an
input or semantic premise of this equation. -/
theorem actual_seed_value (R q rest : ℕ) (h : Handler ChildPort) (node : Node.T) :
    ((DFTModelSavingRecords.stream R).run h
      (rest,((run DFTModelCacheRecords.seed q).val,node))).val=
      recordFold R rest h (UniformFixedNetworkScheduleMachine.scheduleRecords q) node := by
  rw [DFTModelCacheRecords.seed_value]
  exact stream_list_value R rest h _ node

end
end ExactFourierCircuits.DFTModelSavingChronology

import DFTModelSavingNativeBilledSequence

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingChronologyWork
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelSavingChronology
open UniformFixedNetworkScheduleMachine (Record)
open DFTModelSavingNativeBilledSequence (stream_cons_work)
noncomputable section
attribute [local irreducible] DFTModelSavingRecords.stream DFTModelSavingRecords.dispatch

lemma stream_nil_work (R rest : ℕ) (h : Handler ChildPort) (node : Node.T) :
    ((DFTModelSavingRecords.stream R).run h
      (rest,(DFTModelCacheRecords.recordTape [],node))).work=12 := by
  rw [DFTModelSavingCost.stream_run]
  rfl

/-- Appending the actual final padding record preserves chronological billing.
The stream's twelve initial steps are paid once. -/
theorem stream_snoc_work (R rest : ℕ) (h : Handler ChildPort)
    (rs : List Record) (r : Record) (node : Node.T) :
    ((DFTModelSavingRecords.stream R).run h
      (rest,(DFTModelCacheRecords.recordTape (rs++[r]),node))).work=
    ((DFTModelSavingRecords.stream R).run h
      (rest,(DFTModelCacheRecords.recordTape rs,node))).work+
    ((DFTModelSavingRecords.dispatch R).run h
      (rest,(DFTModelCacheRecords.dataTape r.data,recordFold R rest h rs node))).work+22 := by
  induction rs generalizing node with
  | nil=>
    rw [List.nil_append,stream_cons_work,stream_nil_work,stream_nil_work]
    change _=12+((DFTModelSavingRecords.dispatch R).run h
      (rest,(DFTModelCacheRecords.dataTape r.data,node))).work+22
    omega
  | cons a rs ih=>
    rw [List.cons_append,stream_cons_work,stream_cons_work,ih]
    change _=_+((DFTModelSavingRecords.dispatch R).run h
      (rest,(DFTModelCacheRecords.dataTape r.data,recordFold R rest h rs (recordStep R rest h a node)))).work+22
    omega

end
end ExactFourierCircuits.DFTModelSavingChronologyWork

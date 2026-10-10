import DFTModelSavingNativePaddingStepHeader
import UniformPaddingRecordProjections

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSavingNativePaddingStep
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl UniformFixedNetworkScheduleMachine UniformNativeScheduleSemantics
noncomputable section
attribute [local irreducible] DFTModelSavingRecords.dispatch DFTModelSavingRecords.padding

lemma record_value_of_fields (R q rest start count : ℕ) (record : Record)
    (h : Handler DFTModelSavingRecords.Port) (node : Node.T)
    (opcode : record.opcode=5) (columns : record.columns=q)
    (dest : record.dest=start) (size : record.source=count) :
    DFTModelSavingChronology.recordStep R rest h record node=
      (DFTModelSavingNativePaddingFold.steps h q rest start count node).val := by
  let raw:=DFTModelCacheRecords.dataTape record.data
  have fields:=data_header record
  have op:raw.look 0 0=5:=fields.1.trans opcode
  have cols:raw.look 1 0=q:=fields.2.1.trans columns
  have dst:raw.look 3 0=start:=fields.2.2.1.trans dest
  have cnt:raw.look 4 0=count:=fields.2.2.2.trans size
  unfold DFTModelSavingChronology.recordStep
  change (Code.run (DFTModelSavingRecords.dispatch R) h (rest,(raw,node))).val=_
  rw [DFTModelSavingNativePaddingValue.dispatch_value _ _ _ _ _ op,
    DFTModelSavingNativePaddingFold.padding_value,cols,dst,cnt]


theorem record_value (q rest : ℕ) (h : Handler DFTModelSavingRecords.Port) (node : Node.T) :
    DFTModelSavingChronology.recordStep UniformFixedNetwork.W rest h (Instruction.record q .padding) node=
      (DFTModelSavingNativePaddingFold.steps h q rest UniformFixedNetworkScheduleMachine.actualRoles
        (UniformFixedNetwork.W-UniformFixedNetworkScheduleMachine.actualRoles) node).val :=
  record_value_of_fields UniformFixedNetwork.W q rest UniformFixedNetworkScheduleMachine.actualRoles
    (UniformFixedNetwork.W-UniformFixedNetworkScheduleMachine.actualRoles) (Instruction.record q .padding) h node
    (UniformPaddingRecordProjections.opcode q) (UniformPaddingRecordProjections.columns q)
    (UniformPaddingRecordProjections.dest q) (UniformPaddingRecordProjections.source q)

end
end ExactFourierCircuits.DFTModelSavingNativePaddingStep

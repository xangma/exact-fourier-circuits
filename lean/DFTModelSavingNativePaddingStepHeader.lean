import DFTModelSavingNativePaddingFold
import UniformPaddingRecordProjections

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSavingNativePaddingStep
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl UniformFixedNetworkScheduleMachine UniformNativeScheduleSemantics
noncomputable section
attribute [local irreducible] DFTModelSavingRecords.dispatch DFTModelSavingRecords.padding

lemma data_header (r : Record) :
    let raw:=DFTModelCacheRecords.dataTape r.data
    raw.look 0 0=r.opcode ∧ raw.look 1 0=r.columns ∧
      raw.look 3 0=r.dest ∧ raw.look 4 0=r.source := by
  dsimp only
  have field (j : ℕ) (hj : j<8) :=DFTModelSavingNativeControl.dataTape_lookup r.data j
    (by rw [Record.data_length];omega)
  refine ⟨?_,?_,?_,?_⟩
  · simpa [Record.data,Record.header] using field 0 (by decide)
  · simpa [Record.data,Record.header] using field 1 (by decide)
  · simpa [Record.data,Record.header] using field 3 (by decide)
  · simpa [Record.data,Record.header] using field 4 (by decide)


end
end ExactFourierCircuits.DFTModelSavingNativePaddingStep

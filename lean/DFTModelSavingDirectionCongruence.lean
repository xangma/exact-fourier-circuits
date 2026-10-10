import DFTModelSavingDirection
import DFTModelSavingResidualCongruence

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingDirection
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelSavingRecords
noncomputable section
attribute [local irreducible] DFTModelSavingResidual.program

def HandlerEq (q : ℕ) (h h' : Handler Port) : Prop :=
  ∀ (I : ℂ) (bank : Tape DFTModelAffine.Tagged.T),
    (h ((q,I),bank)).val=(h' ((q,I),bank)).val

theorem row_value_congr (q rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T)
    (h h' : Handler Port) (columns : rawTape.look 1 0=q) (same : HandlerEq q h h') :
    (rowBill h rest i rawTape old node).val=(rowBill h' rest i rawTape old node).val := by
  rcases node with ⟨⟨k,I⟩,bank⟩
  apply DFTModelSavingResidualCongruence.value_congr
  intro J v
  change (h ((rawTape.look 1 0,J),v)).val=(h' ((rawTape.look 1 0,J),v)).val
  rw [columns]
  exact same J v

theorem residual_value_congr (q rest : ℕ) (rawTape : Tape ℕ) (node : Node.T)
    (h h' : Handler Port) (columns : rawTape.look 1 0=q) (same : HandlerEq q h h') :
    (Code.run residual h (rest,(rawTape,node))).val=
      (Code.run residual h' (rest,(rawTape,node))).val := by
  rw [residual_run,residual_run]
  apply DFTModelSavingRecords.steps_value_congr
  intro i z
  exact row_value_congr q rest i rawTape node z h h' columns same

end
end ExactFourierCircuits.DFTModelSavingDirection

import DFTModelSavingPadding
import DFTModelSavingDirectionCongruence

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingPadding
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelSavingRecords
noncomputable section
attribute [local irreducible] DFTModelSavingRecords.residual DFTModelCacheRecords.unit

theorem record_column (r : UniformFixedNetworkScheduleMachine.Record) :
    (DFTModelCacheRecords.dataTape r.data).look 1 0=r.columns := by
  simp [DFTModelCacheRecords.dataTape,Tape.look,Tape.tab,
    UniformFixedNetworkScheduleMachine.Record.data,UniformFixedNetworkScheduleMachine.Record.header]

theorem unitTape_columns (q role : ℕ) : ((run DFTModelCacheRecords.unit (q,role)).val).look 1 0=q := by
  rw [DFTModelCacheRecords.unit_value]
  exact record_column (DFTModelCacheRecords.withRole q role UniformRecursiveSavingProgram.unitRecord)

theorem roleWith_value_congr (U : Prog false (p w w) (Ty.a w))
    (q rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T)
    (h h' : Handler Port) (columns : rawTape.look 1 0=q)
    (unitColumns : ∀ a b,((run U (a,b)).val).look 1 0=a)
    (same : DFTModelSavingDirection.HandlerEq q h h') :
    (roleBillWith U h rest i rawTape old node).val=
      (roleBillWith U h' rest i rawTape old node).val := by
  apply DFTModelSavingDirection.residual_value_congr q rest
    ((run U (rawTape.look 1 0,rawTape.look 3 0+i)).val) node h h' _ same
  rw [unitColumns,columns]

theorem role_value_congr (q rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T)
    (h h' : Handler Port) (columns : rawTape.look 1 0=q)
    (same : DFTModelSavingDirection.HandlerEq q h h') :
    (roleBill h rest i rawTape old node).val=(roleBill h' rest i rawTape old node).val :=
  roleWith_value_congr DFTModelCacheRecords.unit q rest i rawTape old node h h' columns
    unitTape_columns same

theorem padding_value_congr (q rest : ℕ) (rawTape : Tape ℕ) (node : Node.T)
    (h h' : Handler Port) (columns : rawTape.look 1 0=q)
    (same : DFTModelSavingDirection.HandlerEq q h h') :
    (Code.run padding h (rest,(rawTape,node))).val=
      (Code.run padding h' (rest,(rawTape,node))).val := by
  rw [padding_run,padding_run]
  apply DFTModelSavingRecords.steps_value_congr
  intro i z
  exact role_value_congr q rest i rawTape node z h h' columns same

end
end ExactFourierCircuits.DFTModelSavingPadding

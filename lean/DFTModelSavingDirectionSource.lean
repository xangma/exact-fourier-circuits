import DFTModelSavingDirection
import DFTModelSavingResidualGeometry

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingDirection
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelSavingRecords
open UniformFixedNetworkScheduleMachine BinaryFrames FramedScheduleWords UniformFixedNetwork
noncomputable section
attribute [local irreducible] DFTModelSavingResidual.program

theorem row_source {R S m : ℕ} (q : ℕ) (e : Fin R ↪ Fin S)
    {old new : Label m} (role : Fin R) (edge : NestedEdge old new)
    (rawTape : Tape ℕ) (source : RawSource (macroRecord q e (.edge old new role edge)) rawTape)
    (i : Fin edge.dimension) (j : Fin m) :
    (row m i.val rawTape).look j.val 0=(edgeVectors edge i j).val := by
  simpa [row,Tape.look,Tape.tab,j.isLt] using macro_bits q e role edge rawTape source i j

theorem row_preserved (h : Handler Port) (rest i k : ℕ) (I : ℂ)
    (rawTape : Tape ℕ) (old : Node.T) (bank : Tape DFTModelAffine.Tagged.T) :
    (rowBill h rest i rawTape old ((k,I),bank)).val.1=(k,I) ∧
    (rowBill h rest i rawTape old ((k,I),bank)).val.2.len=bank.len := by
  exact DFTModelSavingResidualGeometry.preserved h
    (rawTape.look 1 0,(rawTape.look 2 0,(rest,row (rawTape.look 2 0) i rawTape)))
    (rawTape.look 3 0) (rawTape.look 5 0) k I bank

theorem steps_preserved (h : Handler Port) (rest count k : ℕ) (I : ℂ)
    (rawTape : Tape ℕ) (bank : Tape DFTModelAffine.Tagged.T) :
    (steps h rest rawTape ((k,I),bank) count).val.1=(k,I) ∧
    (steps h rest rawTape ((k,I),bank) count).val.2.len=bank.len := by
  induction count with
  | zero => exact ⟨rfl,rfl⟩
  | succ count ih =>
    let prior := (steps h rest rawTape ((k,I),bank) count).val
    have hp : prior.1=(k,I) := ih.1
    have hr := row_preserved h rest count prior.1.1 prior.1.2 rawTape ((k,I),bank) prior.2
    change (rowBill h rest count rawTape ((k,I),bank) prior).val.1=(k,I) ∧
      (rowBill h rest count rawTape ((k,I),bank) prior).val.2.len=bank.len
    exact ⟨hr.1.trans hp,hr.2.trans ih.2⟩

theorem residual_preserved (h : Handler Port) (rest k : ℕ) (I : ℂ)
    (rawTape : Tape ℕ) (bank : Tape DFTModelAffine.Tagged.T) :
    (Code.run residual h (rest,(rawTape,((k,I),bank)))).val.1=(k,I) ∧
    (Code.run residual h (rest,(rawTape,((k,I),bank)))).val.2.len=bank.len := by
  rw [residual_run]
  exact steps_preserved h rest (rawTape.look 6 0) k I rawTape bank

end
end ExactFourierCircuits.DFTModelSavingDirection

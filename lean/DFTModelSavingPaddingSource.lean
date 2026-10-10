import DFTModelSavingPadding
import DFTModelSavingDirectionSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingPadding
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelSavingRecords
noncomputable section
attribute [local irreducible] DFTModelSavingRecords.residual DFTModelCacheRecords.unit

theorem roleWith_preserved (U : Prog false (p w w) (Ty.a w))
    (h : Handler Port) (rest i k : ℕ) (I : ℂ)
    (rawTape : Tape ℕ) (old : Node.T) (bank : Tape DFTModelAffine.Tagged.T) :
    (roleBillWith U h rest i rawTape old ((k,I),bank)).val.1=(k,I) ∧
    (roleBillWith U h rest i rawTape old ((k,I),bank)).val.2.len=bank.len :=
  DFTModelSavingDirection.residual_preserved h rest k I
    ((run U (rawTape.look 1 0,rawTape.look 3 0+i)).val) bank

theorem role_preserved (h : Handler Port) (rest i k : ℕ) (I : ℂ)
    (rawTape : Tape ℕ) (old : Node.T) (bank : Tape DFTModelAffine.Tagged.T) :
    (roleBill h rest i rawTape old ((k,I),bank)).val.1=(k,I) ∧
    (roleBill h rest i rawTape old ((k,I),bank)).val.2.len=bank.len :=
  roleWith_preserved DFTModelCacheRecords.unit h rest i k I rawTape old bank

theorem node_steps_preserved (f : ℕ → Node.T → Bill Node.T)
    (same : ∀ i k (I : ℂ) bank,(f i ((k,I),bank)).val.1=(k,I) ∧
      (f i ((k,I),bank)).val.2.len=bank.len)
    (count k : ℕ) (I : ℂ) (bank : Tape DFTModelAffine.Tagged.T) :
    (Bill.steps ((k,I),bank) f count).val.1=(k,I) ∧
    (Bill.steps ((k,I),bank) f count).val.2.len=bank.len := by
  induction count with
  | zero => exact ⟨rfl,rfl⟩
  | succ count ih =>
    let prior := (Bill.steps ((k,I),bank) f count).val
    have hp : prior.1=(k,I) := ih.1
    have hr := same count prior.1.1 prior.1.2 prior.2
    change (f count prior).val.1=(k,I) ∧ (f count prior).val.2.len=bank.len
    exact ⟨hr.1.trans hp,hr.2.trans ih.2⟩

theorem steps_preserved (h : Handler Port) (rest count k : ℕ) (I : ℂ)
    (rawTape : Tape ℕ) (bank : Tape DFTModelAffine.Tagged.T) :
    (steps h rest rawTape ((k,I),bank) count).val.1=(k,I) ∧
    (steps h rest rawTape ((k,I),bank) count).val.2.len=bank.len :=
  node_steps_preserved (fun i z=>roleBill h rest i rawTape ((k,I),bank) z)
    (fun i kk II bb=>role_preserved h rest i kk II rawTape ((k,I),bank) bb) count k I bank

theorem padding_preserved (h : Handler Port) (rest k : ℕ) (I : ℂ)
    (rawTape : Tape ℕ) (bank : Tape DFTModelAffine.Tagged.T) :
    (Code.run padding h (rest,(rawTape,((k,I),bank)))).val.1=(k,I) ∧
    (Code.run padding h (rest,(rawTape,((k,I),bank)))).val.2.len=bank.len := by
  rw [padding_run]
  exact steps_preserved h rest (rawTape.look 4 0) k I rawTape bank

end
end ExactFourierCircuits.DFTModelSavingPadding

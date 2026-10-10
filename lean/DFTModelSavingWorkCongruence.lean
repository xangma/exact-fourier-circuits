import DFTModelSavingBillCongruence
import DFTModelSavingResidualBilledCongruence
import DFTModelSavingCostRecords

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingWorkCongruence
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine DFTModelSavingRecords
open DFTModelSavingBillCongruence
noncomputable section
attribute [local irreducible] DFTModelSavingResidual.program
  DFTModelSavingRecords.residual DFTModelSavingRecords.padding
  DFTModelCacheRecords.unit DFTModelCacheRecords.seed
  DFTModelSavingScalar.program DFTModelSavingY.program DFTModelRecursiveExchange.program

def HandlerRelated (q : ℕ) (h h' : Handler Port) : Prop :=
  ∀ (I : ℂ) (bank : Tape Tagged.T), Related (h ((q,I),bank)) (h' ((q,I),bank))

lemma row_related (q rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T)
    (h h' : Handler Port) (columns : rawTape.look 1 0=q) (same : HandlerRelated q h h') :
    Related (DFTModelSavingDirection.rowBill h rest i rawTape old node)
      (DFTModelSavingDirection.rowBill h' rest i rawTape old node) := by
  rcases node with ⟨⟨k,I⟩,bank⟩
  apply pay
  apply DFTModelSavingResidualBilledCongruence.value_work_congr
  intro J v
  change Related (h ((rawTape.look 1 0,J),v)) (h' ((rawTape.look 1 0,J),v))
  rw [columns]
  exact same J v

lemma residual_related (q rest : ℕ) (rawTape : Tape ℕ) (node : Node.T)
    (h h' : Handler Port) (columns : rawTape.look 1 0=q) (same : HandlerRelated q h h') :
    Related (Code.run residual h (rest,(rawTape,node)))
      (Code.run residual h' (rest,(rawTape,node))) := by
  rw [DFTModelSavingDirection.residual_run,DFTModelSavingDirection.residual_run]
  apply pay
  apply steps
  intro i _ z
  exact row_related q rest i rawTape node z h h' columns same

lemma roleWith_related (U : Prog false (p w w) (Ty.a w))
    (q rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T)
    (h h' : Handler Port) (columns : rawTape.look 1 0=q)
    (unitColumns : ∀ a b,((run U (a,b)).val).look 1 0=a)
    (same : HandlerRelated q h h') :
    Related (DFTModelSavingPadding.roleBillWith U h rest i rawTape old node)
      (DFTModelSavingPadding.roleBillWith U h' rest i rawTape old node) := by
  apply pay
  apply residual_related q rest _ node h h' _ same
  rw [unitColumns,columns]

lemma role_related (q rest i : ℕ) (rawTape : Tape ℕ) (old node : Node.T)
    (h h' : Handler Port) (columns : rawTape.look 1 0=q) (same : HandlerRelated q h h') :
    Related (DFTModelSavingPadding.roleBill h rest i rawTape old node)
      (DFTModelSavingPadding.roleBill h' rest i rawTape old node) :=
  roleWith_related DFTModelCacheRecords.unit q rest i rawTape old node h h' columns
    DFTModelSavingPadding.unitTape_columns same

lemma padding_related (q rest : ℕ) (rawTape : Tape ℕ) (node : Node.T)
    (h h' : Handler Port) (columns : rawTape.look 1 0=q) (same : HandlerRelated q h h') :
    Related (Code.run padding h (rest,(rawTape,node)))
      (Code.run padding h' (rest,(rawTape,node))) := by
  rw [DFTModelSavingPadding.padding_run,DFTModelSavingPadding.padding_run]
  apply pay
  apply steps
  intro i _ z
  exact role_related q rest i rawTape node z h h' columns same

lemma dispatch_related (R q rest : ℕ) (rawTape : Tape ℕ) (node : Node.T)
    (h h' : Handler Port) (columns : rawTape.look 1 0=q) (same : HandlerRelated q h h') :
    Related ((dispatch R).run h (rest,(rawTape,node)))
      ((dispatch R).run h' (rest,(rawTape,node))) := by
  unfold dispatch
  apply ifz_closed
  · exact residual_related q rest rawTape node h h' columns same
  · apply ifz_closed
    · exact comp _ _ _ _ _ (closed _ _ _ _) (fun _=>closed _ _ _ _)
    · apply ifz_closed
      · exact closed _ _ _ _
      · apply ifz_closed
        · exact closed _ _ _ _
        · apply ifz_closed
          · exact comp _ _ _ _ _ (closed _ _ _ _) (fun _=>closed _ _ _ _)
          · apply ifz_closed
            · exact padding_related q rest rawTape node h h' columns same
            · exact closed _ _ _ _

lemma stream_related (R q rest : ℕ) (rs : Tape (Tape ℕ)) (node : Node.T)
    (h h' : Handler Port) (columns : ∀i<rs.len,(rs.look i (Tape.empty ℕ)).look 1 0=q)
    (same : HandlerRelated q h h') :
    Related ((stream R).run h (rest,(rs,node))) ((stream R).run h' (rest,(rs,node))) := by
  rw [DFTModelSavingCost.stream_run,DFTModelSavingCost.stream_run]
  apply pay
  apply steps
  intro i hi z
  exact dispatch_related R q rest _ z h h' (columns i hi) same

end
end ExactFourierCircuits.DFTModelSavingWorkCongruence

import DFTModelSavingCostRecords
import DFTModelSavingShape

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelClockControl UniformFixedNetworkScheduleMachine
open scoped BigOperators
noncomputable section
attribute [local irreducible] DFTModelSavingRecords.dispatch

lemma recordTape_lookup (rs : List Record) (i : ℕ) (hi : i<rs.length) :
    (DFTModelCacheRecords.recordTape rs).look i (Tape.empty ℕ)=
      DFTModelCacheRecords.dataTape rs[i].data := by
  simp [DFTModelCacheRecords.recordTape,Tape.look,Tape.tab,hi]

lemma recordSteps_preserved (R rest : ℕ) (rs : Tape (Tape ℕ)) (node : Node.T)
    (h : Handler DFTModelSavingRecords.Port) (i : ℕ) :
    DFTModelSavingShape.Preserves node (recordSteps R rest rs node h i).val :=
  DFTModelSavingShape.steps_preserves node _
    (fun _ _=>DFTModelSavingShape.dispatch_preserves R h _) i

lemma sum_range_lookup {α : Type} (rs : List α) (blank : α) (f : α→ℕ) :
    (∑i∈Finset.range rs.length,f ((rs[i]?).getD blank))=(rs.map f).sum := by
  rw [←Fin.sum_univ_eq_sum_range]
  have eq : (fun i:Fin rs.length=>f ((rs[i.val]?).getD blank))=
      (fun i:Fin rs.length=>f rs[i.val]) := by
    funext i
    rw [List.getElem?_eq_getElem i.isLt]
    rfl
  rw [eq,←List.sum_ofFn,List.ofFn_getElem_eq_map]

end
end ExactFourierCircuits.DFTModelSavingCost

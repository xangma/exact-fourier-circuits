import DFTModelSavingCostDirection
import DFTModelSavingPaddingSource
import UniformRecursivePaddingUnitEdge

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelClockControl
open UniformFixedNetworkScheduleMachine BinaryFrames FramedScheduleWords UniformFixedNetwork
noncomputable section
attribute [local irreducible] DFTModelCacheRecords.unit DFTModelSavingRecords.residual
  DFTModelSavingRecords.padding

def singletonEmbedding (a : ℕ) : Fin 1 ↪ Fin (a+1) :=
  ⟨fun _=>⟨a,Nat.lt_succ_self a⟩,fun _ _ _=>Subsingleton.elim _ _⟩

theorem patch_withRole (r : Record) (q a : ℕ) :
    UniformRecursivePaddingControl.patchRecord r q a=DFTModelCacheRecords.withRole q a r := rfl

/-- The unit source is the table freshly executed by upstream Code; no
preprinted unit directions are assumed. -/
theorem unit_source (q a : ℕ) :
    DFTModelSavingDirection.RawSource
      (macroRecord q (singletonEmbedding a)
        (.edge _ _ (0:Fin 1) (UniformRecursivePaddingUnitEdge.unitEdge ExplicitSeedBudget.m)))
      (run DFTModelCacheRecords.unit (q,a)).val := by
  rw [UniformRecursivePaddingUnitEdge.macro_fixed,patch_withRole,DFTModelCacheRecords.unit_value]
  exact DFTModelSavingDirection.dataTape_source _

end
end ExactFourierCircuits.DFTModelSavingCost

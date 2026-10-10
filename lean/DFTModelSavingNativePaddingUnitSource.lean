import DFTModelSavingNativePaddingBoot
import DFTModelSavingNativePaddingFold
import DFTModelSavingNativeDirectionLoopValue
import DFTModelSavingCostPaddingSource

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSavingNativePaddingUnitSource
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelSavingNativePaddingBoot
noncomputable section
attribute [local irreducible] DFTModelCacheRecords.unit DFTModelSavingRecords.residual

/-- Factor all record rewriting before specializing the enormous fixed payload. -/
theorem source_from (q width R : ℕ) (role : Fin R)
    (record : UniformFixedNetworkScheduleMachine.Record)
    (U : Prog false (p w w) (Ty.a w))
    (printed : (run U (q,role.val)).val=DFTModelCacheRecords.dataTape
      (DFTModelCacheRecords.withRole q role.val record).data)
    (same : macRecord q width R role=UniformRecursivePaddingControl.patchRecord record q role.val) :
    DFTModelSavingDirection.RawSource (macRecord q width R role) (run U (q,role.val)).val := by
  rw [printed,same,DFTModelSavingCost.patch_withRole]
  exact DFTModelSavingDirection.dataTape_source _

theorem source (q width R : ℕ) (role : Fin R) (shape : width+1=ExplicitSeedBudget.m) :
    DFTModelSavingDirection.RawSource (macRecord q width R role)
      (run DFTModelCacheRecords.unit (q,role.val)).val := by
  apply source_from q width R role UniformRecursiveSavingProgram.unitRecord DFTModelCacheRecords.unit
    (DFTModelCacheRecords.unit_value q role.val)
  unfold macRecord
  rw [shape]
  exact UniformRecursivePaddingUnitEdge.macro_fixed q (Function.Embedding.refl _) role

theorem dimension (q width R : ℕ) (role : Fin R) (raw : Tape ℕ)
    (src : DFTModelSavingDirection.RawSource (macRecord q width R role) raw) :
    raw.look 6 0=width+1 :=
  (DFTModelSavingDirection.macro_headers q (Function.Embedding.refl _) role
    (UniformRecursivePaddingUnitEdge.unitEdge (width+1)) raw src).2.2.2.2

theorem residual_value (h : Handler DFTModelSavingRecords.Port) (rest count : ℕ)
    (raw : Tape ℕ) (node : Node.T) (dim : raw.look 6 0=count) :
    (Code.run DFTModelSavingRecords.residual h (rest,(raw,node))).val=
      DFTModelSavingNativeDirection.rows h rest raw (List.finRange count) node := by
  rw [DFTModelSavingDirection.residual_run]
  change (DFTModelSavingDirection.steps h rest raw node (raw.look 6 0)).val=_
  rw [dim,DFTModelSavingNativeDirection.rows_all]

theorem role_value (h : Handler DFTModelSavingRecords.Port) (q rest index : ℕ) (node : Node.T) :
    (DFTModelSavingNativePaddingFold.role h q rest index node).val=
      (Code.run DFTModelSavingRecords.residual h
        (rest,((run DFTModelCacheRecords.unit (q,index)).val,node))).val := rfl

theorem value (q width r R : ℕ) (role : Fin R) (shape : width+1=ExplicitSeedBudget.m)
    (h : Handler DFTModelSavingRecords.Port) (node : Node.T) :
    (DFTModelSavingNativePaddingFold.role h q r role.val node).val=
      DFTModelSavingNativeDirection.rows h r
        (run DFTModelCacheRecords.unit (q,role.val)).val (List.finRange (width+1)) node :=
  (role_value h q r role.val node).trans
    (residual_value h r (width+1) (run DFTModelCacheRecords.unit (q,role.val)).val node
      (dimension q width R role _ (source q width R role shape)))

end
end ExactFourierCircuits.DFTModelSavingNativePaddingUnitSource

import DFTModelSavingNativeDirectionBilledFold
import DFTModelSavingNativePaddingUnitSource
import DFTModelSavingCostBilledLoops

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativePaddingBilledWork
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl
open scoped BigOperators
noncomputable section
attribute [local irreducible] DFTModelCacheRecords.unit DFTModelSavingRecords.residual

/-- The chronological prefix bill is the exact sum of the actual direction steps. -/
theorem prefixWork_all (h : Handler DFTModelSavingRecords.Port) (rest count : ℕ)
    (raw : Tape ℕ) (node : Node.T) :
    DFTModelSavingNativeDirection.prefixWork h rest raw node (List.finRange count)=
      ∑j∈Finset.range count,
        ((DFTModelSavingDirection.rowBill h rest j raw node
          (DFTModelSavingDirection.steps h rest raw node j).val).work+1) := by
  have sum : DFTModelSavingNativeDirection.prefixWork h rest raw node (List.finRange count)=
      ∑j : Fin count, ((DFTModelSavingDirection.rowBill h rest j.val raw node
        (DFTModelSavingDirection.steps h rest raw node j.val).val).work+1) := by
    simpa only [DFTModelSavingNativeDirection.prefixWork,List.finRange,List.map_ofFn,Function.comp_def]
      using Fin.sum_ofFn (fun j : Fin count=>
        (DFTModelSavingDirection.rowBill h rest j.val raw node
          (DFTModelSavingDirection.steps h rest raw node j.val).val).work+1)
  rw [sum]
  exact Fin.sum_univ_eq_sum_range (fun j=>
    (DFTModelSavingDirection.rowBill h rest j raw node
      (DFTModelSavingDirection.steps h rest raw node j).val).work+1) count

/-- Only the physically printed dimension is needed; the fixed unit payload stays opaque. -/
theorem residual_work_prefix (h : Handler DFTModelSavingRecords.Port) (rest count : ℕ)
    (raw : Tape ℕ) (node : Node.T) (dimension : raw.look 6 0=count) :
    (Code.run DFTModelSavingRecords.residual h (rest,(raw,node))).work=
      DFTModelSavingNativeDirection.prefixWork h rest raw node (List.finRange count)+14 := by
  rw [DFTModelSavingDirection.residual_run]
  change (DFTModelSavingDirection.steps h rest raw node (raw.look 6 0)).work+13=_
  rw [dimension,DFTModelSavingCost.direction_steps_actual_work,prefixWork_all]
  omega

theorem role_work (h : Handler DFTModelSavingRecords.Port) (q rest index count : ℕ)
    (node : Node.T)
    (dimension : (run DFTModelCacheRecords.unit (q,index)).val.look 6 0=count) :
    (DFTModelSavingNativePaddingFold.role h q rest index node).work=
      DFTModelSavingNativeDirection.prefixWork h rest
        (run DFTModelCacheRecords.unit (q,index)).val node (List.finRange count)+14 :=
  residual_work_prefix h rest count _ node dimension

/-- The dimension comes from the actual fresh unit printer and its source theorem. -/
theorem role_work_unit (q width rest R : ℕ) (role : Fin R)
    (h : Handler DFTModelSavingRecords.Port) (node : Node.T)
    (shape : width+1=ExplicitSeedBudget.m) :
    (DFTModelSavingNativePaddingFold.role h q rest role.val node).work=
      DFTModelSavingNativeDirection.prefixWork h rest
        (run DFTModelCacheRecords.unit (q,role.val)).val node (List.finRange (width+1))+14 :=
  role_work h q rest role.val (width+1) node
    (DFTModelSavingNativePaddingUnitSource.dimension q width R role _
      (DFTModelSavingNativePaddingUnitSource.source q width R role shape))

/-- The one real padding-role prefix pays the fresh unit print and wrapper
without increasing the recursive coefficient. -/
theorem role_billed (q width rest R : ℕ) (role : Fin R)
    (h : Handler DFTModelSavingRecords.Port) (node : Node.T)
    (shape : width+1=ExplicitSeedBudget.m) (K dt : ℕ)
    (fixed : DFTModelSavingCost.unitAllowance+52≤K)
    (directions : DFTModelSavingNativeDirection.prefixWork h rest
      (run DFTModelCacheRecords.unit (q,role.val)).val node (List.finRange (width+1))≤K*dt) :
    (DFTModelSavingNativePaddingFold.role h q rest role.val node).work+
      DFTModelSavingCost.unitAllowance+38≤K*(47+dt+4+6) := by
  rw [role_work_unit q width rest R role h node shape]
  have firstBound : K≤K*57 := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith only [fixed,directions,firstBound]

end
end ExactFourierCircuits.DFTModelSavingNativePaddingBilledWork

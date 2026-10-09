import DFTModelCRTBounds
import DFTModelCRTSelectedGeometry
import UniformFinalPhysicalTableExecution

set_option autoImplicit false

/-! Actual selected AP/BI correspondence.  The typed producer receives explicit
readonly radix/idempotent/cofactor metadata.  Producing that metadata in the
upstream machine is a separate obligation; no precomputed AP or BI is supplied. -/
namespace ExactFourierCircuits.DFTModelCRT
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformCRTTraversalCycle UniformSelectedPhysicalCRT UniformMachine
open scoped BigOperators
noncomputable section

def selectedRows (n : ℕ) : Tape (ℕ × (ℕ × ℕ)) :=
  ⟨UniformAllAxisSeedPreparation.axisCount n,
    fun i => (radices n i,(alphaWeights n i,betaWeights n i))⟩

def selectedArgs (n : ℕ) : Args.T := (0,(len n,selectedRows n))
def selectedInput (n : ℕ) : (p w Args).T :=
  (UniformAllAxisSeedPreparation.axisCount n,selectedArgs n)

theorem selected_rows (n : ℕ) (i : Fin (UniformAllAxisSeedPreparation.axisCount n)) :
    (selectedArgs n).2.2.look ((selectedArgs n).1+i.val) (0,(0,0)) =
      (radices n i,(alphaWeights n i,betaWeights n i)) := by
  simp [selectedArgs,selectedRows,Tape.look,i.isLt]

theorem selected_prefix (n : ℕ) :
    prefixTable (UniformAllAxisSeedPreparation.axisCount n) (selectedArgs n) =
      selectedCartesian n := prefix_selectedCartesian n _ rfl (selected_rows n)

theorem selected_length (n : ℕ) :
    (prefixTable (UniformAllAxisSeedPreparation.axisCount n) (selectedArgs n)).len=len n := by
  rw [selected_prefix,selectedCartesian_length]

theorem selected_rows_two {n : ℕ} (hn : 0<n) :
    RowsTwo (UniformAllAxisSeedPreparation.axisCount n) (selectedArgs n) := by
  intro i hi
  have h := selected_rows n ⟨i,hi⟩
  rw [h]
  exact UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn _

theorem selected_weights_bound (n : ℕ) :
    WeightsBound (UniformAllAxisSeedPreparation.axisCount n) (selectedArgs n) (len n) := by
  intro i hi
  rw [selected_rows n ⟨i,hi⟩]
  constructor
  · have h : alphaWeights n ⟨i,hi⟩<len n := by
      simpa only [UniformSelectedCRT.radices_product] using
        UniformCRT.idempotent_lt (radices n) (UniformSelectedCRT.radix_pos n) ⟨i,hi⟩
    exact h.le
  · rw [betaWeights,UniformCRT.cofactor_eq_div _ _ (UniformSelectedCRT.radix_pos n ⟨i,hi⟩),
      UniformSelectedCRT.radices_product]
    exact Nat.div_le_self _ _

/-- One actual closed typed program produces the same physical AP and inverse-Beta
banks as the actual literal53, for every positive input length. -/
theorem selected_values (n : ℕ) (j : Fin (len n)) :
    (run program (selectedInput n)).val.1.look j.val 0=(physicalAlpha n j).val ∧
    (run program (selectedInput n)).val.2.look j.val 0=((physicalBeta n).symm j).val := by
  constructor
  · rw [selectedInput,program_alpha_value,selected_prefix]
    rw [Tape.look_of_lt _ _ (by simpa only [Tape.tab,selectedCartesian_length] using j.isLt)]
    change ((selectedCartesian n).look j.val (0,0)).1=(physicalAlpha n j).val
    exact congrArg Prod.fst (selectedCartesian_value n j)
  · apply program_inverse_value _ _ (selected_length n) (physicalBeta n)
    intro i
    rw [selected_prefix]
    exact congrArg Prod.snd (selectedCartesian_value n i)

theorem selected_work {n : ℕ} (hn : 0<n) :
    (run program (selectedInput n)).work≤300*(len n+1) := by
  simpa only [selectedInput,selected_length] using
    program_work_linear _ _ (selected_rows_two hn)

theorem selected_peak {n : ℕ} (hn : 0<n) :
    (run program (selectedInput n)).peak≤(len n+1)^2 := by
  have size := prefix_axes_le _ _ (selected_rows_two hn)
  rw [selected_length] at size
  apply program_peak_le _ _ (len n) (by omega) rfl
  · change 0+UniformAllAxisSeedPreparation.axisCount n≤len n
    omega
  · exact selected_rows_two hn
  · exact selected_weights_bound n
  · exact (selected_length n).le

theorem selected_valid (n : ℕ) : (run program (selectedInput n)).valid :=
  program_valid _ _

theorem selected_output_lengths (n : ℕ) :
    (run program (selectedInput n)).val.1.len=len n ∧
    (run program (selectedInput n)).val.2.len=len n := by
  constructor
  · rw [selectedInput,program_alpha_value]
    exact selected_length n
  · change (run inverseBeta (run tables (selectedInput n)).val).val.len=len n
    rw [selectedInput,tables_value,inverse_value]
    exact (sow_iter_len _ _ _ _).trans (selected_length n)

/-- Constant-factor comparison of the two proved linear stage budgets. -/
theorem selected_work_source_budget {n : ℕ} (hn : 0<n) :
    (run program (selectedInput n)).work≤
      5*(60*(len n+UniformAllAxisSeedPreparation.axisCount n+1)) := by
  have h := selected_work hn
  omega

/-- Operational endpoint agreement with the genuine stage53, retaining its
actual frames and charged source bound.  The typed work is linear in the same
volume; this is an algorithm refinement, not a store-by-store simulation. -/
theorem actual_stage (c : UniformJointAllocation.Constants) {n : ℕ} (hn : 0<n)
    (x : Fin n → ℂ) (s : State) (pc : s.pc=0)
    (args : UniformFastPhysicalCRTMachine.Args (UniformAllAxisSeedPreparation.axisCount n)
      (len n) (UniformFinalPhysicalTableGeometry.addresses c n) s)
    (core : UniformAxisCachePreparationRetention.Core n x s)
    (wb : WordBound (UniformJointAllocation.envelope c n) s) :
    ∃ticks u, BoundedExecution UniformFastPhysicalCRTMachine.program n x
        (UniformJointAllocation.envelope c n) s ticks u ∧
      ticks≤60*(len n+UniformAllAxisSeedPreparation.axisCount n+1) ∧ u.pc=52 ∧
      UniformFastPhysicalCRTMachine.Frame s u ∧
      (∀j : Fin (len n),
        u.natHeap ((UniformFinalPhysicalTableGeometry.addresses c n).physicalAlpha+j.val)=
          some ((run program (selectedInput n)).val.1.look j.val 0) ∧
        u.natHeap ((UniformFinalPhysicalTableGeometry.addresses c n).inverseBeta+j.val)=
          some ((run program (selectedInput n)).val.2.look j.val 0)) ∧
      (run program (selectedInput n)).valid ∧
      (run program (selectedInput n)).work≤300*(len n+1) ∧
      (run program (selectedInput n)).peak≤(len n+1)^2 := by
  obtain ⟨ticks,u,h,cost,up,_,_,frame,_,ap,bi⟩ :=
    UniformFinalPhysicalTableExecution.execution c hn x s pc args core wb
  refine ⟨ticks,u,h,cost,up,frame,?_,selected_valid n,selected_work hn,selected_peak hn⟩
  intro j
  rw [(selected_values n j).1,(selected_values n j).2]
  exact ⟨ap j,bi j⟩

end
end ExactFourierCircuits.DFTModelCRT

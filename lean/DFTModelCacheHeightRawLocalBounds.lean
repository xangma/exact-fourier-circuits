import DFTModelCacheHeightRawBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheHeightRaw
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

/-- Selection work depends on the size of a generated depth bucket, rather than
on the physical addresses stored in the selected rows. -/
theorem directory_slotCount (n A C P G d : ℕ) (enabled : Bool)
    (t ord : Tape ℕ) (depth : ℕ → ℕ) (hd : d ≤ G) :
    DFTModelCacheHeight.slotCount
      (DFTModelCacheHeight.input n A C P d enabled t ord
        (Tape.tab (G+2) (fun j => UniformDAGBucketMachine.offset G j depth))) =
      2*(UniformDAGBucketMachine.selected G d depth).length := by
  change 2*((Tape.tab (G+2) (fun j => UniformDAGBucketMachine.offset G j depth)).look (d+1) 0 -
    (Tape.tab (G+2) (fun j => UniformDAGBucketMachine.offset G j depth)).look d 0) = _
  rw [DFTModelCacheHeight.tab_read _ _ _ (by omega),
    DFTModelCacheHeight.tab_read _ _ _ (by omega),
    UniformDAGBucketMachine.offset_succ, Nat.add_sub_cancel_left]

/-- Out-of-directory requests have zero saturated count; in-directory requests
inspect at most two operand slots for each original gate occurrence. -/
theorem directory_slotCount_le (n A C P G d : ℕ) (enabled : Bool)
    (t ord : Tape ℕ) (depth : ℕ → ℕ) :
    DFTModelCacheHeight.slotCount
      (DFTModelCacheHeight.input n A C P d enabled t ord
        (Tape.tab (G+2) (fun j => UniformDAGBucketMachine.offset G j depth))) ≤ 2*G := by
  by_cases hd : d ≤ G
  · rw [directory_slotCount n A C P G d enabled t ord depth hd]
    exact Nat.mul_le_mul_left 2 (UniformDAGBucketMachine.selected_length G d depth)
  · have finish : (Tape.tab (G+2) (fun j => UniformDAGBucketMachine.offset G j depth)).look (d+1) 0 = 0 := by
      unfold Tape.look
      split
      · rename_i h
        have : d+1 < G+2 := h
        omega
      · rfl
    change 2*((Tape.tab (G+2) (fun j => UniformDAGBucketMachine.offset G j depth)).look (d+1) 0 -
      (Tape.tab (G+2) (fun j => UniformDAGBucketMachine.offset G j depth)).look d 0) ≤ _
    rw [finish, Nat.zero_sub, Nat.mul_zero]
    exact Nat.zero_le _

/-- The closed raw producer creates the directory internally. No restriction
on the request height or physical A/C/P bases is needed for the work bound. -/
theorem selected_slotCount_le (a e A C P d : ℕ) (enabled : Bool) :
    DFTModelCacheHeight.slotCount
      (selectedInput (A,(C,(P,(d,if enabled then 1 else 0)))) e
        (run DFTModelCacheBucketRaw.program (a,e)).val) ≤ 2*(dag a e).size := by
  rw [DFTModelCacheBucketRaw.program_value]
  exact directory_slotCount_le e A C P (dag a e).size d enabled
    (run DFTModelCacheTopology.program (a,e)).val.2.2
    (Tape.tab (dag a e).size (fun j =>
      (UniformDAGBucketMachine.order (dag a e).size
        (UniformDAGBucketMachine.typedDepth (dag a e).program))[j]?.getD 0))
    (UniformDAGBucketMachine.typedDepth (dag a e).program)

def localWorkBudget (a e : ℕ) : ℕ :=
  DFTModelCacheBucketRaw.workBudget a e +
    DFTModelCacheHeight.workBudget (2*(dag a e).size) + 25

/-- Actual charged work is independent of global physical allocation bases. -/
theorem program_work_local (a e A C P d : ℕ) (enabled : Bool) :
    (run program ((A,(C,(P,(d,if enabled then 1 else 0)))),(a,e))).work ≤
      localWorkBudget a e := by
  obtain ⟨u,ticks,source,bucket⟩ := DFTModelCacheBucketRaw.execution a e
  have height := (DFTModelCacheHeight.program_work _).trans
    (height_work_mono (selected_slotCount_le a e A C P d enabled))
  have base := bucket.2.1
  rw [program_run]
  change (run DFTModelCacheBucketRaw.program (a,e)).work +
    (run DFTModelCacheHeight.program
      (selectedInput (A,(C,(P,(d,if enabled then 1 else 0)))) e
        (run DFTModelCacheBucketRaw.program (a,e)).val)).work + 25 ≤ _
  unfold localWorkBudget
  omega

theorem localWorkBudget_polynomial (a e : ℕ) :
    localWorkBudget a e ≤ DFTModelCacheBucketRaw.workBudget a e +
      1200*(2*(dag a e).size+1)^2 + 25 := by
  have h := DFTModelCacheHeight.workBudget_polynomial (2*(dag a e).size)
  unfold localWorkBudget
  omega

theorem program_work_local_polynomial (a e A C P d : ℕ) (enabled : Bool) :
    (run program ((A,(C,(P,(d,if enabled then 1 else 0)))),(a,e))).work ≤
      DFTModelCacheBucketRaw.workBudget a e + 1200*(2*(dag a e).size+1)^2 + 25 :=
  (program_work_local a e A C P d enabled).trans (localWorkBudget_polynomial a e)

/-- Preserve the genuine topology witness and established address-sensitive
peak bound, while charging only local topology size for selection work. -/
theorem execution_local (a e A C P d : ℕ) (enabled : Bool) :
    ∃ u ticks, DFTModelCacheTopology.Result a e u ticks ∧
      DFTModelCacheMatchingNat.Budget
        (run program ((A,(C,(P,(d,if enabled then 1 else 0)))),(a,e)))
        (localWorkBudget a e) (peakBudget a e A C P d) := by
  obtain ⟨u,ticks,source,budget⟩ := execution a e A C P d enabled
  exact ⟨u,ticks,source,budget.1,program_work_local a e A C P d enabled,budget.2.2⟩

end
end ExactFourierCircuits.DFTModelCacheHeightRaw

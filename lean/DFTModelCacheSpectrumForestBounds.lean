import DFTModelCacheSpectrumForestCorrect

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheSpectrumForest
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section
attribute [local irreducible] program cell DFTModelCacheTraversal.program
  DFTModelCacheRectanglePreparation.program Bill.tab

def workBudget (r D : ℕ) : ℕ := 100000*(r+1)^5+
  r^2*(DFTModelCacheRectanglePreparation.rowBudget r D+30)+19
def peakBudget (r o D : ℕ) : ℕ := max (D+2) (DFTModelCacheTraversal.peakBudget r o)

theorem program_work (r o D : ℕ) (z : ℂ) :
    (run program ((r,o),(D,z))).work≤workBudget r D := by
  rw [program_run]
  let forest:=(run DFTModelCacheTraversal.program (r,o)).val
  let L:=forest.2.len
  have producer:=DFTModelCacheTraversal.program_work r o
  have count: L≤r^2 := (DFTModelCacheTraversal.program_lengths r o).2
  have cells:∀i∈Finset.range L,
      (run cell ((((r,o),(D,z)),forest),i)).work≤
        DFTModelCacheRectanglePreparation.rowBudget r D+24 := by
    intro i hi
    have hi':i<(run DFTModelCacheTraversal.program (r,o)).val.2.len:=Finset.mem_range.mp hi
    obtain ⟨q,source,eq⟩:=traversal_produced r o ⟨i,hi'⟩
    rw [cell_run]
    change (run DFTModelCacheRectanglePreparation.program
      ((r,forest.2.look i DFTModelCacheDescriptor.Row7.blank),(D,z))).work+24≤_
    rw [Tape.look_of_lt _ _ hi',eq]
    exact Nat.add_le_add_right (DFTModelCacheRectanglePreparation.program_uniform_work z source) 24
  have sum:=Finset.sum_le_sum cells
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at sum
  change (run DFTModelCacheTraversal.program (r,o)).work+
    ((Bill.tab L DFTModelCacheRectanglePreparation.Output.blank
      (fun i=>run cell ((((r,o),(D,z)),forest),i))).work+1)+14≤_
  rw [ModelEquivalenceInterpreter.tab_work]
  have scaled:=Nat.mul_le_mul_right
    (DFTModelCacheRectanglePreparation.rowBudget r D+30) count
  dsimp only [workBudget]
  nlinarith

theorem program_peak (r o D : ℕ) (z : ℂ) :
    (run program ((r,o),(D,z))).peak≤peakBudget r o D := by
  rw [program_run]
  let forest:=(run DFTModelCacheTraversal.program (r,o)).val
  let L:=forest.2.len
  let B:=peakBudget r o D
  have producer:(run DFTModelCacheTraversal.program (r,o)).peak≤B :=
    (DFTModelCacheTraversal.program_peak r o).trans (le_max_right _ _)
  have count:L≤B := by
    have length:=(DFTModelCacheTraversal.program_lengths r o).2
    have pow: r+1≤(r+1)^4 := le_self_pow₀ (by omega) (by decide)
    have fit:r^2≤DFTModelCacheTraversal.peakBudget r o := by
      unfold DFTModelCacheTraversal.peakBudget
      nlinarith
    exact (length.trans fit).trans (le_max_right _ _)
  have cells:(Finset.range L).sup
      (fun i=>(run cell ((((r,o),(D,z)),forest),i)).peak)≤B := by
    apply Finset.sup_le
    intro i hi
    have hi':i<(run DFTModelCacheTraversal.program (r,o)).val.2.len:=Finset.mem_range.mp hi
    obtain ⟨q,source,eq⟩:=traversal_produced r o ⟨i,hi'⟩
    rw [cell_run]
    change max (run DFTModelCacheRectanglePreparation.program
      ((r,forest.2.look i DFTModelCacheDescriptor.Row7.blank),(D,z))).peak 0≤_
    rw [Tape.look_of_lt _ _ hi',eq,max_zero]
    have bound:=DFTModelCacheRectanglePreparation.program_peak (D:=D) z source
    have width:=(DFTModelCacheRectanglePreparation.produced_width source).2.2
    have pow:r+1≤(r+1)^4 := le_self_pow₀ (by omega) (by decide)
    have fit:r+7*DFTModelCacheRectanglePreparation.width q+7≤
        DFTModelCacheTraversal.peakBudget r o := by
      unfold DFTModelCacheTraversal.peakBudget
      omega
    exact bound.trans (max_le_max (le_refl _) fit)
  change max (max (run DFTModelCacheTraversal.program (r,o)).peak
    (max (Bill.tab L DFTModelCacheRectanglePreparation.Output.blank
      (fun i=>run cell ((((r,o),(D,z)),forest),i))).peak 0)) L≤B
  rw [ModelEquivalenceInterpreter.tab_peak]
  exact max_le (max_le producer (max_le (max_le count cells) (Nat.zero_le _))) count

theorem selected_valid (n : ℕ) (hn : 0<n)
    (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) (o : ℕ) :
    (run program ((UniformAllAxisSeedPreparation.radix n j,o),
      (UniformMasterRootMachine.order n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)))).valid :=
  program_valid _ _ _ (DFTModelCacheRectanglePreparation.selected_master n hn j)

end
end ExactFourierCircuits.DFTModelCacheSpectrumForest

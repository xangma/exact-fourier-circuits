import DFTModelCacheAllAxisForestsCorrect

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheAllAxisForests
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
open scoped BigOperators
noncomputable section
attribute [local irreducible] program setup body DFTModelCacheAxisRoots.program
  DFTModelRoot.program DFTModelCacheSpectrumForest.program

def axisBudgets (n : ℕ) : ℕ :=
  ∑i∈Finset.range (UniformAllAxisSeedPreparation.axisCount n),
    DFTModelCacheSpectrumForest.workBudget ((DFTModelCacheAxisRoots.values n).look i (0,0)).1
      (UniformMasterRootMachine.order n)

def workBudget (n : ℕ) : ℕ := DFTModelCacheAxisRoots.budget n+
  6*UniformMasterRootMachine.preparationBudget n+14+
  20*UniformAllAxisSeedPreparation.axisCount n+axisBudgets n

theorem axisBudgets_eq (n : ℕ) : axisBudgets n=
    ∑j:Fin (UniformAllAxisSeedPreparation.axisCount n),
      DFTModelCacheSpectrumForest.workBudget (UniformAllAxisSeedPreparation.radix n j)
        (UniformMasterRootMachine.order n) := by
  unfold axisBudgets
  symm
  calc
    _=∑j:Fin (UniformAllAxisSeedPreparation.axisCount n),
      DFTModelCacheSpectrumForest.workBudget ((DFTModelCacheAxisRoots.values n).look j.val (0,0)).1
        (UniformMasterRootMachine.order n) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [root_lookup n j]
    _=_ := Fin.sum_univ_eq_sum_range
      (fun i=>DFTModelCacheSpectrumForest.workBudget ((DFTModelCacheAxisRoots.values n).look i (0,0)).1
        (UniformMasterRootMachine.order n)) (UniformAllAxisSeedPreparation.axisCount n)

theorem program_work (n : ℕ) (hn : 0<n) :
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).work≤workBudget n := by
  rw [program,comp_run,setup_run]
  change (run DFTModelCacheAxisRoots.program _).work+(run DFTModelRoot.program n).work+5+
    (run body _).work+1≤_
  rw [DFTModelCacheAxisRoots.selected_value n hn,(DFTModelRoot.actual_master_order n hn).1,body_work]
  have producer:=DFTModelCacheAxisRoots.selected_work n hn
    (OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))
  have root:=(DFTModelRoot.actual_master_order n hn).2.2.1
  have sumBound : (∑i∈Finset.range (UniformAllAxisSeedPreparation.axisCount n),
      (run DFTModelCacheSpectrumForest.program
        ((((DFTModelCacheAxisRoots.values n).look i (0,0)).1,0),
          (UniformMasterRootMachine.order n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)))).work)
      ≤axisBudgets n := by
    apply Finset.sum_le_sum
    intro i _
    exact DFTModelCacheSpectrumForest.program_work _ _ _ _
  change (run DFTModelCacheAxisRoots.program _).work+(run DFTModelRoot.program n).work+5+
    (8+20*UniformAllAxisSeedPreparation.axisCount n+_)+1≤_
  change (∑i∈Finset.range (DFTModelCacheAxisRoots.values n).len,
    (run DFTModelCacheSpectrumForest.program
      ((((DFTModelCacheAxisRoots.values n).look i (0,0)).1,0),
        (UniformMasterRootMachine.order n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)))).work)≤axisBudgets n at sumBound
  unfold workBudget
  omega

def peakBudget (n : ℕ) : ℕ := max ((n+2)^13)
  (max (UniformMasterRootMachine.order n+2) (100000*(4*n+1)^4))

theorem program_peak (n : ℕ) (hn : 0<n) :
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).peak≤peakBudget n := by
  have producer:=DFTModelCacheAxisRoots.selected_peak n hn
    (OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))
  have root:=(DFTModelRoot.actual_master_order n hn).2.2.2
  have pow : (n+2)^12≤(n+2)^13 := Nat.pow_le_pow_right (by omega) (by omega)
  have count:=DFTModelCRTMetadata.selected_count_le hn
  have volume:=(UniformWorkingLength.workingLength_upper hn).le
  change UniformCRTTraversalCycle.len n≤4*n at volume
  have countFit : (DFTModelCacheAxisRoots.values n).len≤peakBudget n := by
    have lin : 4*n≤(n+2)^13 := by
      have square : 4*n≤(n+2)^2 := by nlinarith
      exact square.trans (Nat.pow_le_pow_right (by omega) (by omega))
    change UniformWorkingLength.axisCount n+1≤_
    exact (show UniformWorkingLength.axisCount n+1≤(n+2)^13 by omega).trans (le_max_left _ _)
  rw [program,comp_run,setup_run]
  simp only [Bill.pass,Bill.pay,max_zero]
  change max (max (run DFTModelCacheAxisRoots.program _).peak (run DFTModelRoot.program n).peak)
    (run body _).peak≤_
  refine max_le (max_le (producer.trans (le_max_left _ _))
    ((root.trans pow).trans (le_max_left _ _))) ?_
  rw [DFTModelCacheAxisRoots.selected_value n hn,(DFTModelRoot.actual_master_order n hn).1]
  apply body_peak _ _ _ _ countFit
  intro i hi
  let j:Fin (UniformAllAxisSeedPreparation.axisCount n):=⟨i,hi⟩
  rw [root_lookup n j]
  have bound:=DFTModelCacheSpectrumForest.program_peak
    (UniformAllAxisSeedPreparation.radix n j) 0 (UniformMasterRootMachine.order n)
    (OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))
  have radixBound:UniformAllAxisSeedPreparation.radix n j≤4*n :=
    (UniformGlobalLocalPreparation.radix_le_length n j).trans volume
  have scaled:=Nat.mul_le_mul_left 100000
    (Nat.pow_le_pow_left (show UniformAllAxisSeedPreparation.radix n j+1≤4*n+1 by omega) 4)
  apply bound.trans
  change max (UniformMasterRootMachine.order n+2)
    (100000*(UniformAllAxisSeedPreparation.radix n j+1)^4+0)≤_
  exact (max_le_max (le_refl _) (by omega)).trans (le_max_right _ _)

theorem peakBudget_polynomial (n : ℕ) (hn : 0<n) : peakBudget n≤(n+2)^24 := by
  have hd:=((UniformMasterRootMachine.order_bounds hn).2.le).trans
    (UniformMasterRootMachine.wordBound_setup hn).2.2.2
  have pow13 : (n+2)^13≤(n+2)^24 := Nat.pow_le_pow_right (by omega) (by omega)
  have hd13 : UniformMasterRootMachine.order n+2≤(n+2)^13 := by
    have hp : 1≤(n+2)^12 := Nat.one_le_pow _ _ (by omega)
    have hm:=Nat.mul_le_mul_right ((n+2)^12) (show 3≤n+2 by omega)
    rw [pow_succ]
    nlinarith
  have width : 4*n+1≤(n+2)^3 := by nlinarith [sq_nonneg (n*n)]
  have power : (4*n+1)^4≤(n+2)^12 := by
    simpa only [←pow_mul] using Nat.pow_le_pow_left width 4
  have constant : 100000≤(n+2)^12 :=
    (show 100000≤3^12 by decide).trans (Nat.pow_le_pow_left (by omega) 12)
  have scaled:=Nat.mul_le_mul constant power
  rw [←pow_add] at scaled
  exact max_le pow13 (max_le (hd13.trans pow13) scaled)

theorem specification (n : ℕ) (hn : 0<n) :
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val=values n ∧
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).valid ∧
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).work≤workBudget n ∧
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).peak≤(n+2)^24 :=
  ⟨program_value n hn,program_valid n hn,program_work n hn,
    (program_peak n hn).trans (peakBudget_polynomial n hn)⟩

end
end ExactFourierCircuits.DFTModelCacheAllAxisForests

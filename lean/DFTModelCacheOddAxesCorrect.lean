import DFTModelCacheOddAxes
import DFTModelCacheLiteral

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheOddAxes
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
open scoped BigOperators
noncomputable section

attribute [local irreducible] applyOdd DFTModelCacheAxisRoots.program
  DFTModelCacheKernelBanks.program

def values (n : ℕ) : Tape DFTModelCacheKernelBanks.Output.T :=
  Tape.tab (UniformWorkingLength.axisCount n) (fun j=>
    (DFTModelCacheForest.values (UniformWorkingLength.oddPrime j)
      (OAI.ExactFourier.zeta (UniformWorkingLength.oddPrime j)),
     DFTModelCacheKernelNewton.gValues (UniformWorkingLength.oddPrime j)
      (OAI.ExactFourier.zeta (UniformWorkingLength.oddPrime j))))

def budget (n : ℕ) : ℕ := DFTModelCacheAxisRoots.budget n+9+
  6*UniformWorkingLength.axisCount n+
  200*∑j∈Finset.range (UniformWorkingLength.axisCount n),
    (UniformWorkingLength.oddPrime j+1)^2

theorem root_lookup (n j : ℕ) (hj : j<UniformWorkingLength.axisCount n) :
    (DFTModelCacheAxisRoots.values n).look j (0,0)=
      (UniformWorkingLength.oddPrime j,
        OAI.ExactFourier.zeta (UniformWorkingLength.oddPrime j)) := by
  rw [Tape.look_of_lt _ _ (show j<(DFTModelCacheAxisRoots.values n).len by
    change j<UniformWorkingLength.axisCount n+1;omega)]
  change (UniformSelectedCRT.radices n ⟨j,_⟩,
    OAI.ExactFourier.zeta (UniformSelectedCRT.radices n ⟨j,_⟩))=_
  have h : (⟨j,show j<UniformWorkingLength.axisCount n+1 by omega⟩ :
      Fin (UniformWorkingLength.axisCount n+1))=(⟨j,hj⟩ : Fin _).castSucc := rfl
  rw [h]
  simp only [UniformSelectedCRT.radices,Fin.snoc_castSucc]

theorem odd_prime_le_length (n j : ℕ) (hn : 0<n) (hj : j<UniformWorkingLength.axisCount n) :
    UniformWorkingLength.oddPrime j≤UniformCRTTraversalCycle.len n := by
  let i : Fin (UniformWorkingLength.axisCount n+1):=(⟨j,hj⟩ : Fin _).castSucc
  have hd : UniformSelectedCRT.radices n i∣UniformCRTTraversalCycle.len n := by
    have d:=Finset.dvd_prod_of_mem (UniformSelectedCRT.radices n) (Finset.mem_univ i)
    rwa [UniformSelectedCRT.radices_product] at d
  have hl : 0<UniformCRTTraversalCycle.len n := by
    change 0<UniformWorkingLength.workingLength n
    exact UniformWorkingLength.workingLength_pos hn
  simpa only [i,UniformSelectedCRT.radices,Fin.snoc_castSucc] using Nat.le_of_dvd hl hd

theorem program_value (n : ℕ) (hn : 0<n) :
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val=values n := by
  change (run (applyOdd DFTModelCacheKernelBanks.program)
    (run DFTModelCacheAxisRoots.program _).val).val=_
  rw [DFTModelCacheAxisRoots.selected_value n hn,apply_value]
  change Tape.tab (UniformWorkingLength.axisCount n) _=values n
  unfold values
  apply DFTModelCacheLiteral.tab_ext
  intro j hj
  rw [root_lookup n j hj,DFTModelCacheKernelBanks.program_value _ _
    (UniformWorkingLength.oddPrime_prime j).pos]

theorem program_valid (n : ℕ) (hn : 0<n) :
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).valid := by
  change (run DFTModelCacheAxisRoots.program _).valid ∧
    (run (applyOdd DFTModelCacheKernelBanks.program)
      (run DFTModelCacheAxisRoots.program _).val).valid
  refine ⟨DFTModelCacheAxisRoots.selected_valid n hn _,?_⟩
  rw [DFTModelCacheAxisRoots.selected_value n hn]
  apply apply_valid
  intro j hj
  change j<UniformWorkingLength.axisCount n at hj
  rw [root_lookup n j hj]
  apply DFTModelCacheKernelBanks.program_valid (UniformWorkingLength.oddPrime_prime j).pos
  exact Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt (UniformWorkingLength.oddPrime_prime j).pos)

theorem program_work (n : ℕ) (hn : 0<n) :
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).work≤budget n := by
  change (run DFTModelCacheAxisRoots.program _).work+
    (run (applyOdd DFTModelCacheKernelBanks.program)
      (run DFTModelCacheAxisRoots.program _).val).work+1≤_
  rw [DFTModelCacheAxisRoots.selected_value n hn,apply_work]
  have hlen : (DFTModelCacheAxisRoots.values n).len-1=UniformWorkingLength.axisCount n := rfl
  rw [hlen]
  have hr:=DFTModelCacheAxisRoots.selected_work n hn
    (OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))
  have hs : (∑j∈Finset.range (UniformWorkingLength.axisCount n),
      (run DFTModelCacheKernelBanks.program
        ((DFTModelCacheAxisRoots.values n).look j (0,0))).work)≤
      200*∑j∈Finset.range (UniformWorkingLength.axisCount n),
        (UniformWorkingLength.oddPrime j+1)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    rw [root_lookup n j (Finset.mem_range.mp hj)]
    exact DFTModelCacheKernelBanks.program_work _ _
  change (run DFTModelCacheAxisRoots.program _).work+
    (8+6*UniformWorkingLength.axisCount n+_) +1≤_
  unfold budget
  omega

theorem program_peak (n : ℕ) (hn : 0<n) :
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).peak≤(n+2)^13 := by
  have hr:=DFTModelCacheAxisRoots.selected_peak n hn
    (OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))
  have hc:=DFTModelCRTMetadata.selected_count_le hn
  have hv:=(UniformWorkingLength.workingLength_upper hn).le
  change UniformCRTTraversalCycle.len n≤4*n at hv
  have hb : 4*n≤(n+2)^13 := by
    have h2 : 4*n≤(n+2)^2 := by nlinarith
    exact h2.trans (Nat.pow_le_pow_right (by omega) (by omega))
  change max (max (run DFTModelCacheAxisRoots.program _).peak
    (run (applyOdd DFTModelCacheKernelBanks.program)
      (run DFTModelCacheAxisRoots.program _).val).peak) 0≤_
  refine max_le (max_le hr ?_) (Nat.zero_le _)
  rw [DFTModelCacheAxisRoots.selected_value n hn]
  apply apply_peak
  · change UniformWorkingLength.axisCount n+1≤_
    omega
  · exact Nat.one_le_pow _ _ (by omega)
  · intro j hj
    change j<UniformWorkingLength.axisCount n at hj
    rw [root_lookup n j hj]
    exact (DFTModelCacheKernelBanks.program_peak _ _).trans
      ((odd_prime_le_length n j hn hj).trans (by omega))

theorem specification (n : ℕ) (hn : 0<n) :
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val=values n ∧
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).valid ∧
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).work≤budget n ∧
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).peak≤(n+2)^13 :=
  ⟨program_value n hn,program_valid n hn,program_work n hn,program_peak n hn⟩

end
end ExactFourierCircuits.DFTModelCacheOddAxes

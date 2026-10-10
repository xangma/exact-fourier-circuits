import DFTModelCacheAxisRoots

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheAxisRoots
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section

attribute [local irreducible] setup bank program DFTModelWorkingHeaders.program DFTModelRoot.program

def values (n : ℕ) : Tape (ℕ × ℂ) :=
  ⟨UniformWorkingLength.axisCount n+1,fun i=>
    (UniformCRTTraversalCycle.radices n i,OAI.ExactFourier.zeta (UniformCRTTraversalCycle.radices n i))⟩

def budget (n : ℕ) : ℕ := 16*UniformWorkingCompletion.preparationBudget n+
  6*UniformMasterRootMachine.preparationBudget n+18+
  (UniformWorkingLength.axisCount n+1)*(40*(Nat.log2 (UniformMasterRootMachine.order n+1)+1)+82)

theorem program_run (n : ℕ) (z : ℂ) : run program (n,z)=
    ⟨(run bank ((run DFTModelWorkingHeaders.program n).val,((run DFTModelRoot.program n).val,z))).val,
      (run DFTModelWorkingHeaders.program n).work+(run DFTModelRoot.program n).work+
        (run bank ((run DFTModelWorkingHeaders.program n).val,((run DFTModelRoot.program n).val,z))).work+8,
      max (max (run DFTModelWorkingHeaders.program n).peak (run DFTModelRoot.program n).peak)
        (run bank ((run DFTModelWorkingHeaders.program n).val,((run DFTModelRoot.program n).val,z))).peak,
      ((run DFTModelWorkingHeaders.program n).valid ∧ (run DFTModelRoot.program n).valid) ∧
        (run bank ((run DFTModelWorkingHeaders.program n).val,((run DFTModelRoot.program n).val,z))).valid⟩ := by
  rw [program,comp_run,setup_run]
  simp only [Bill.pass,Bill.pay,max_zero]
  congr 1
  omega

theorem program_source_value (n : ℕ) (hn : 0<n) (z : ℂ) :
    (run program (n,z)).val=
      (run bank (DFTModelCRTMetadata.selectedInput n,(UniformMasterRootMachine.order n,z))).val := by
  rw [program_run,(DFTModelWorkingHeaders.actual_headers n hn).1,
    (DFTModelRoot.actual_master_order n hn).1]

theorem selected_radix_dvd (n : ℕ) (i : Fin (UniformWorkingLength.axisCount n+1)) :
    UniformCRTTraversalCycle.radices n i∣UniformMasterRootMachine.order n := by
  have h : UniformCRTTraversalCycle.radices n i∣∏j,UniformCRTTraversalCycle.radices n j :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  rw [UniformSelectedCRT.radices_product] at h
  exact h.trans (UniformMasterRootMachine.divisor_orders n).2.1

theorem selected_value (n : ℕ) (hn : 0<n) :
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val=values n := by
  rw [program_source_value n hn,bank_value]
  change (⟨UniformWorkingLength.axisCount n+1,fun i=>
    (DFTModelCRTMetadata.radixValue (DFTModelCRTMetadata.selectedInput n) i.val,
      OAI.ExactFourier.zeta (UniformMasterRootMachine.order n)^
        (UniformMasterRootMachine.order n/DFTModelCRTMetadata.radixValue
          (DFTModelCRTMetadata.selectedInput n) i.val))⟩ : Tape (ℕ × ℂ))=values n
  apply congrArg (fun f=> (⟨UniformWorkingLength.axisCount n+1,f⟩ : Tape (ℕ × ℂ)))
  funext i
  rw [DFTModelCRTMetadata.selected_radix]
  rw [UniformRoots.specifiedRoot_divisor_power _ _ (UniformMasterRootMachine.order_bounds hn).1
    (UniformSelectedCRT.radix_pos n i) (selected_radix_dvd n i)]

theorem selected_valid (n : ℕ) (hn : 0<n) (z : ℂ) : (run program (n,z)).valid := by
  rw [program,comp_run,setup_run]
  change ((run DFTModelWorkingHeaders.program n).valid ∧ (run DFTModelRoot.program n).valid) ∧
    (run bank _).valid
  exact ⟨⟨(DFTModelWorkingHeaders.actual_headers n hn).2.1,
    (DFTModelRoot.actual_master_order n hn).2.1⟩,bank_valid _ _ _⟩

theorem selected_work (n : ℕ) (hn : 0<n) (z : ℂ) :
    (run program (n,z)).work≤budget n := by
  rw [program_run,(DFTModelWorkingHeaders.actual_headers n hn).1,
    (DFTModelRoot.actual_master_order n hn).1]
  have h:=bank_work (DFTModelCRTMetadata.selectedInput n) (UniformMasterRootMachine.order n) z
  have hw:=(DFTModelWorkingHeaders.actual_headers n hn).2.2.1
  have hr:=(DFTModelRoot.actual_master_order n hn).2.2.1
  change (run DFTModelWorkingHeaders.program n).work+(run DFTModelRoot.program n).work+
    (run bank _).work+8≤_
  change (run bank _).work≤10+(UniformWorkingLength.axisCount n+1)*
    (40*(Nat.log2 (UniformMasterRootMachine.order n+1)+1)+82) at h
  unfold budget
  omega

theorem selected_peak (n : ℕ) (hn : 0<n) (z : ℂ) :
    (run program (n,z)).peak≤(n+2)^13 := by
  rw [program_run,(DFTModelWorkingHeaders.actual_headers n hn).1,
    (DFTModelRoot.actual_master_order n hn).1]
  have hb:=bank_peak (DFTModelCRTMetadata.selectedInput n) (UniformMasterRootMachine.order n) z
  have hh:=DFTModelWorkingHeaders.peak_bound n hn
  have hr:=(DFTModelRoot.actual_master_order n hn).2.2.2
  have hd:=((UniformMasterRootMachine.order_bounds hn).2.le).trans
    (UniformMasterRootMachine.wordBound_setup hn).2.2.2
  have hc:=DFTModelCRTMetadata.selected_count_le hn
  have hv:=(UniformWorkingLength.workingLength_upper hn).le
  change UniformCRTTraversalCycle.len n≤4*n at hv
  have hbase : 4*n≤(n+2)^12 := by
    have h2 : 4*n≤(n+2)^2 := by nlinarith
    exact h2.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hlarge : (n+2)^12+2≤(n+2)^13 := by
    have hp : 1≤(n+2)^12 := Nat.one_le_pow _ _ (by omega)
    have hm:=Nat.mul_le_mul_right ((n+2)^12) (show 3≤n+2 by omega)
    rw [pow_succ] at *
    nlinarith
  change (run bank _).peak ≤ max (UniformWorkingLength.axisCount n+1)
    (UniformMasterRootMachine.order n+2) at hb
  change max (max (run DFTModelWorkingHeaders.program n).peak
    (run DFTModelRoot.program n).peak) (run bank _).peak≤_
  exact max_le (max_le (by omega) (by omega))
    (hb.trans (max_le (by omega) (by omega)))

theorem specification (n : ℕ) (hn : 0<n) :
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val=values n ∧
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).valid ∧
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).work≤budget n ∧
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).peak≤(n+2)^13 :=
  ⟨selected_value n hn,selected_valid n hn _,selected_work n hn _,selected_peak n hn _⟩

end
end ExactFourierCircuits.DFTModelCacheAxisRoots

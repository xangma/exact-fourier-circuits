import DFTModelOuterPreparation

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelOuterPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

attribute [local irreducible] DFTModelRoot.program DFTModelRoot.workingLength
  DFTModelRootExtraction.halfAngle DFTModelChirpTables.program header

theorem length_peak_le_master (n : ℕ) :
    (run DFTModelRoot.workingLength n).peak≤(run DFTModelRoot.program n).peak := by
  rw [DFTModelRoot.program_bill]
  simp only [Bill.pass,Bill.one,Bill.pay]
  omega

theorem halfAngle_peak_bound {n : ℕ} (hn : 0<n) (z : ℂ) :
    (run DFTModelRootExtraction.halfAngle (n,(UniformMasterRootMachine.order n,z))).peak≤(n+2)^13 := by
  have h := DFTModelRootExtraction.halfAngle_peak n (UniformMasterRootMachine.order n) z
  have hD := ((UniformMasterRootMachine.order_bounds hn).2.le).trans
    (UniformMasterRootMachine.wordBound_setup hn).2.2.2
  have hnB : 2*n≤(n+2)^12 := by
    have hs := (UniformMasterRootMachine.wordBound_setup hn).2.2.1
    omega
  have hB : 2≤(n+2)^12 := by omega
  have hp : 3*(n+2)^12≤(n+2)^13 := by
    calc
      _≤(n+2)*(n+2)^12 := Nat.mul_le_mul_right _ (by omega)
      _=(n+2)^13 := (Nat.mul_comm _ _).trans (pow_succ (n+2) 12).symm
  omega

theorem header_valid {n : ℕ} (hn : 0<n) (z : ℂ) : (run header (n,z)).valid := by
  unfold header
  change (run lengthPair (n,z)).valid ∧ (run halfRoot (n,z)).valid ∧ True
  rw [lengthPair_run,halfRoot_run]
  exact ⟨⟨(DFTModelRoot.workingLength_spec n hn).2.2.2,trivial⟩,
    ⟨(DFTModelRoot.actual_master_order n hn).2.1,
      DFTModelRootExtraction.halfAngle_valid _ _ _⟩,trivial⟩

theorem header_peak {n : ℕ} (hn : 0<n) (z : ℂ) :
    (run header (n,z)).peak≤(n+2)^13 := by
  unfold header
  change max (run lengthPair (n,z)).peak (max (run halfRoot (n,z)).peak 0)≤_
  rw [lengthPair_run,halfRoot_run]
  simp only [Bill.pass,Bill.pay,Bill.one,max_zero]
  rw [(DFTModelRoot.actual_master_order n hn).1]
  have hL := (length_peak_le_master n).trans ((DFTModelRoot.actual_master_order n hn).2.2.2)
  have hD := (DFTModelRoot.actual_master_order n hn).2.2.2
  have hroot := halfAngle_peak_bound hn z
  have hp : (n+2)^12≤(n+2)^13 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem program_peak {n : ℕ} (hn : 0<n) (z : ℂ) :
    (run program (n,z)).peak≤(n+2)^13 := by
  change max (max (run header (n,z)).peak
    (run DFTModelChirpTables.program (run header (n,z)).val).peak) 0≤_
  have hh := header_peak hn z
  have ht := DFTModelChirpTables.program_peak n
    (run DFTModelRoot.workingLength n).val (run halfRoot (n,z)).val
  have hv : (run header (n,z)).val=((n,(run DFTModelRoot.workingLength n).val),(run halfRoot (n,z)).val) := by
    unfold header
    change ((run lengthPair (n,z)).val,(run halfRoot (n,z)).val)=_
    rw [lengthPair_run]
    rfl
  rw [hv]
  rw [(DFTModelRoot.workingLength_spec n hn).1] at ht ⊢
  have hL := UniformWorkingLength.workingLength_upper hn
  have hbase : n+UniformWorkingLength.workingLength n+2≤(n+2)^2 := by nlinarith
  have hp := Nat.pow_le_pow_left hbase 2
  have he : ((n+2)^2)^2=(n+2)^4 := by ring
  rw [he] at hp
  have h413 : (n+2)^4≤(n+2)^13 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem program_source_value {n : ℕ} (hn : 0<n) :
    (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val=
      (run DFTModelChirpTables.program ((n,UniformWorkingLength.workingLength n),
        OAI.ExactFourier.zeta (2*n))).val := by
  change (run DFTModelChirpTables.program (run header _).val).val=_
  rw [header_value hn]

/-- The same source preparation runs from its genuine initial state. All bank
values and physical layout addresses are proved, not supplied to the theorem. -/
theorem source_preparation {n : ℕ} (hn : 0<n) (x : Fin n → ℂ) :
    ∃t u,UniformMachine.BoundedExecution UniformNormalizationPreparation.fullProgram n x
      ((n+2)^19) UniformMachine.initial t u ∧
      DFTModelChirpTables.SourceMatch x
        (run program (n,OAI.ExactFourier.zeta (UniformMasterRootMachine.order n))).val u ∧
      t≤UniformNormalizationPreparation.fullPreparationBudget n := by
  rw [program_source_value hn]
  exact DFTModelChirpTables.source_preparation hn x

end
end ExactFourierCircuits.DFTModelOuterPreparation

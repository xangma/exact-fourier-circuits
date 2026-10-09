import DFTModelWorkingHeadersProgram

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelWorkingHeaders
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

attribute [local irreducible] select DFTModelRoot.workingLength repack

theorem program_spec (n : ℕ) (hn : 0<n) :
    (run program n).val=DFTModelCRTMetadata.selectedInput n ∧
    (run program n).work≤16*UniformWorkingCompletion.preparationBudget n ∧
    (run program n).peak ≤ max (DFTModelRoot.selectionPeak n) (4*n) ∧
    (run program n).valid := by
  obtain ⟨lv,lw,lp,ld⟩ := DFTModelRoot.workingLength_spec n hn
  obtain ⟨sv,sw,sp,sd⟩ := select_spec n hn
  rw [program_bill]
  generalize hl : run DFTModelRoot.workingLength n=lenBill at lv lw lp ld ⊢
  generalize hs : run select n=selBill at sv sw sp sd ⊢
  dsimp only [Bill.pass,Bill.one,Bill.pay]
  rw [lv,sv,repack_run]
  dsimp only [Bill.val,Bill.work,Bill.peak,Bill.valid]
  rw [binary_quotient]
  simp only [Nat.max_zero]
  have hell : UniformWorkingLength.axisCount n≤2*n := by
    have h := UniformWorkingLength.firstExceed_bound n
    unfold UniformWorkingLength.axisCount
    omega
  have hbinary : UniformWorkingLength.binaryFactor n≤4*n := by
    rw [←binary_quotient]
    exact (Nat.div_le_self _ _).trans (UniformWorkingLength.workingLength_upper hn).le
  have htape : (suffix (UniformWorkingLength.axisCount n) 0).len≤4*n := by
    change UniformWorkingLength.axisCount n-0≤4*n
    omega
  refine ⟨?_,?_,?_,⟨⟨ld,⟨sd,True.intro⟩⟩,True.intro⟩⟩
  · unfold DFTModelCRTMetadata.selectedInput UniformCRTTraversalCycle.len
    change ((suffix (UniformWorkingLength.axisCount n) 0).len,
      (UniformWorkingLength.workingLength n,
        (UniformWorkingLength.binaryFactor n,suffix (UniformWorkingLength.axisCount n) 0)))=_
    simp only [suffix,Tape.tab,Nat.sub_zero,Nat.zero_add]
  · have hb : 21≤2*UniformWorkingCompletion.preparationBudget n := by
      unfold UniformWorkingCompletion.preparationBudget
      have h : 0<(UniformWorkingLength.axisCount n+2)^4 := pow_pos (by omega) _
      omega
    omega
  · exact max_le (max_le lp (sp.trans (le_max_left _ _)))
      ((max_le htape hbinary).trans (le_max_right _ _))

theorem peak_bound (n : ℕ) (hn : 0<n) : (run program n).peak≤(n+2)^12 := by
  have hpow : 1024≤(n+2)^9 := by
    have h := Nat.pow_le_pow_left (show 3≤n+2 by omega) 9
    norm_num at h
    omega
  have hselection : DFTModelRoot.selectionPeak n≤(n+2)^12 := by
    calc
      _≤1024*(n+2)^3 := DFTModelRoot.selectionPeak_polynomial n
      _≤(n+2)^9*(n+2)^3 := Nat.mul_le_mul_right _ hpow
      _=(n+2)^12 := by rw [←pow_add]
  have hn4 : 4*n≤(n+2)^12 := by
    have h2 : 4*n≤(n+2)^2 := by nlinarith
    exact h2.trans (Nat.pow_le_pow_right (by omega) (by omega))
  exact (program_spec n hn).2.2.1.trans (max_le hselection hn4)

/-- This producer needs only the integer n, not supplied selected primes or metadata. -/
theorem actual_headers (n : ℕ) (hn : 0<n) :
    (run program n).val=DFTModelCRTMetadata.selectedInput n ∧
    (run program n).valid ∧
    (run program n).work≤16*UniformWorkingCompletion.preparationBudget n ∧
    (run program n).peak≤(n+2)^12 :=
  ⟨(program_spec n hn).1,(program_spec n hn).2.2.2,
    (program_spec n hn).2.1,peak_bound n hn⟩

/-- Equality to the headers and cells of a genuine initial WorkingCompletion run. -/
theorem actual_preparation (n : ℕ) (hn : 0<n) (x : Fin n→ℂ) :
    ∃ticks s,UniformMachine.BoundedExecution UniformWorkingCompletion.program n x
        ((n+2)^9) UniformMachine.initial ticks s ∧
      s.pc=45 ∧ DFTModelCRTMetadata.sourceInput s=(run program n).val ∧
      ticks≤UniformWorkingCompletion.preparationBudget n ∧
      (run program n).valid ∧
      (run program n).work≤16*UniformWorkingCompletion.preparationBudget n ∧
      (run program n).peak≤(n+2)^12 := by
  obtain ⟨ticks,s,execution,ready,pc,_,_,_,_,_,cost⟩ :=
    UniformWorkingCompletion.preparation_execution hn x
  obtain ⟨value,valid,work,peak⟩ := actual_headers n hn
  exact ⟨ticks,s,execution,pc,(DFTModelCRTMetadata.sourceInput_eq ready).trans value.symm,
    cost,valid,work,peak⟩

theorem work_isBigO_preparationBudget :
    (fun n : ℕ => ((run program n).work : ℝ)) =O[Filter.atTop]
      (fun n : ℕ => (UniformWorkingCompletion.preparationBudget n : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 16
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have h := (actual_headers n (by omega)).2.2.1
  have hreal : ((run program n).work : ℝ)≤
      16*(UniformWorkingCompletion.preparationBudget n : ℝ) := by exact_mod_cast h
  simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _)] using hreal

theorem work_isLittleO_input :
    (fun n : ℕ => ((run program n).work : ℝ)) =o[Filter.atTop]
      (fun n : ℕ => (n : ℝ)) :=
  work_isBigO_preparationBudget.trans_isLittleO
    UniformWorkingCompletion.preparationBudget_isLittleO_input

end
end ExactFourierCircuits.DFTModelWorkingHeaders

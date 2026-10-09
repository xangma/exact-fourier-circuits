import DFTModelRootLength

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelRoot
open OAI.PowerSaving.RAM Ty
noncomputable section

/-- Closed integer algorithm for our actual master-root order, with no supplied L. -/
def program : Prog false w w := .comp (.fork (.atom .id) workingLength) order

theorem pairThen_bill (f : Prog false w w) (g : Prog false (p w w) w) (n : ℕ) :
    run (.comp (.fork (.atom .id) f) g) n =
      (((run f n).pass (fun L => Bill.one (n, L))).pass (run g)).pay 2 0 := by
  rw [code_comp, code_fork]
  change (((Bill.one n).pass (fun y => (run f n).pass (fun z => Bill.one (y, z)))).pass
    (run g)).pay 1 0 = _
  simp [Bill.one, Bill.pass, Bill.pay, Nat.add_comm]
  omega

theorem program_bill (n : ℕ) : run program n =
    (((run workingLength n).pass (fun L => Bill.one (n, L))).pass (run order)).pay 2 0 :=
  pairThen_bill workingLength order n

theorem program_spec (n : ℕ) (hn : 0 < n) :
    (run program n).val = UniformMasterRootMachine.order n ∧
    (run program n).work ≤ 6 * UniformMasterRootMachine.preparationBudget n ∧
    (run program n).peak ≤
      max (max (selectionPeak n) (4 * n)) (UniformMasterRootMachine.order n) ∧
    (run program n).valid := by
  obtain ⟨lv, lw, lp, ld⟩ := workingLength_spec n hn
  obtain ⟨ov, ow, op, od⟩ := order_spec n (UniformWorkingLength.workingLength n) hn
    (UniformWorkingLength.workingLength_pos hn)
  rw [program_bill]
  generalize hl : run workingLength n = lenBill at *
  generalize ho : run order = ord at *
  dsimp only [Bill.pass, Bill.one, Bill.pay]
  simp only [Nat.max_zero]
  rw [lv]
  refine ⟨ov, ?_, ?_, ⟨⟨ld, True.intro⟩, od⟩⟩
  · rw [ow]
    unfold UniformMasterRootMachine.preparationBudget
    omega
  · rw [op]
    exact max_le (lp.trans (le_max_left _ _)) (le_max_right _ _)

theorem selectionPeak_polynomial (n : ℕ) : selectionPeak n ≤ 1024 * (n + 2) ^ 3 := by
  unfold selectionPeak UniformWorkingPreparation.candidateLimit
  nlinarith [Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2)]

theorem program_peak_bound (n : ℕ) (hn : 0 < n) : (run program n).peak ≤ (n + 2) ^ 12 := by
  have h := (program_spec n hn).2.2.1
  have hpow : 1024 ≤ (n + 2) ^ 9 := by
    have hp := Nat.pow_le_pow_left (show 3 ≤ n + 2 by omega) 9
    norm_num at hp
    omega
  have hselection : selectionPeak n ≤ (n + 2) ^ 12 := by
    calc
      selectionPeak n ≤ 1024 * (n + 2) ^ 3 := selectionPeak_polynomial n
      _ ≤ (n + 2) ^ 9 * (n + 2) ^ 3 := Nat.mul_le_mul_right _ hpow
      _ = (n + 2) ^ 12 := by rw [← pow_add]
  obtain ⟨_, _, h128, h1024⟩ := UniformMasterRootMachine.wordBound_setup hn
  have horder := ((UniformMasterRootMachine.order_bounds hn).2.le).trans h1024
  exact h.trans (max_le (max_le hselection (by omega)) horder)

/-- No oracle for n ↦ D: `program` is the explicit finite upstream syntax above. -/
theorem actual_master_order (n : ℕ) (hn : 0 < n) :
    (run program n).val = UniformMasterRootMachine.order n ∧
    (run program n).valid ∧
    (run program n).work ≤ 6 * UniformMasterRootMachine.preparationBudget n ∧
    (run program n).peak ≤ (n + 2) ^ 12 :=
  ⟨(program_spec n hn).1, (program_spec n hn).2.2.2,
    (program_spec n hn).2.1, program_peak_bound n hn⟩

theorem program_one : (run program 1).val = 128 ∧ (run program 1).valid :=
  ⟨(program_spec 1 (by decide)).1.trans selected_order_one,
    (program_spec 1 (by decide)).2.2.2⟩

/-- The upstream integer output equals the sole order in an actual initial-state run. -/
theorem master_execution_bridge (n : ℕ) (hn : 0 < n) (x : Fin n → ℂ) :
    ∃ t s, UniformMachine.BoundedExecution UniformMasterRootMachine.program n x
        ((n + 2) ^ 12) UniformMachine.initial t s ∧
      s.natReg 24 = (run program n).val ∧
      s.rootOrders = [(run program n).val] ∧
      s.scalarReg 0 = ⟨OAI.ExactFourier.zeta (run program n).val, false⟩ ∧
      t ≤ UniformMasterRootMachine.preparationBudget n ∧
      (run program n).valid ∧
      (run program n).work ≤ 6 * UniformMasterRootMachine.preparationBudget n ∧
      (run program n).peak ≤ (n + 2) ^ 12 := by
  obtain ⟨t, s, runRAM, master, _, _, _, _, _, time⟩ :=
    UniformMasterRootMachine.master_execution hn x
  obtain ⟨value, valid, work, peak⟩ := actual_master_order n hn
  refine ⟨t, s, runRAM, master.2.1.trans value.symm, ?_, ?_, time, valid, work, peak⟩
  · rw [value]
    exact master.2.2.2.2.2
  · rw [value]
    exact master.2.2.2.2.1

theorem work_isBigO_preparationBudget :
    (fun n : ℕ => ((run program n).work : ℝ)) =O[Filter.atTop]
      (fun n : ℕ => (UniformMasterRootMachine.preparationBudget n : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 6
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have h := (actual_master_order n (by omega)).2.2.1
  have hreal : ((run program n).work : ℝ) ≤
      6 * (UniformMasterRootMachine.preparationBudget n : ℝ) := by exact_mod_cast h
  simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _)] using hreal

theorem work_isLittleO_input :
    (fun n : ℕ => ((run program n).work : ℝ)) =o[Filter.atTop]
      (fun n : ℕ => (n : ℝ)) :=
  work_isBigO_preparationBudget.trans_isLittleO
    UniformMasterRootMachine.preparationBudget_isLittleO_input

end
end ExactFourierCircuits.DFTModelRoot

import DFTModelRoot

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelRoot
open OAI.PowerSaving.RAM Ty
noncomputable section

def partialProduct : Prog false (p w w) w :=
  .comp (.fork
    (.comp (.fork (.atom (.lit 2)) (.atom .fst)) (.atom (.int .mul)))
    (.atom .snd)) (.atom (.int .mul))

/-- The working-length producer is separate. This is its genuine integer suffix. -/
def order : Prog false (p w w) w :=
  .comp (.fork partialProduct (.comp (.atom .snd) factor)) (.atom (.int .mul))

theorem partial_run (n L : ℕ) :
    run partialProduct (n, L) = ⟨2 * n * L, 9, max (max 2 (2 * n)) (2 * n * L), True⟩ := by
  simp [partialProduct, Code.run, Atom.run, NOp.run, Bill.word, Bill.one, Bill.pass,
    Bill.pay, max_assoc]

theorem order_bill (n L : ℕ) : run order (n, L) =
    ⟨2 * n * L * (run factor L).val,
     (run factor L).work + 14,
     max (max (max 2 (2 * n)) (2 * n * L))
       (max (run factor L).peak (2 * n * L * (run factor L).val)),
     (run factor L).valid⟩ := by
  change ((((run partialProduct (n, L)).pass (fun a =>
    (((Bill.one L).pass (run factor)).pay 1 0).pass
      (fun b => Bill.one (a, b)))).pass
    (fun ab => Bill.word (ab.1 * ab.2))).pay 1 0) = _
  rw [partial_run]
  simp [Bill.word, Bill.one, Bill.pass, Bill.pay, Nat.add_assoc, max_assoc]
  omega

theorem order_spec (n L : ℕ) (hn : 0 < n) (hL : 0 < L) :
    (run order (n, L)).val = UniformBatching.masterRootOrder n L ∧
    (run order (n, L)).work = 18 * UniformBatching.rootBits L + 40 ∧
    (run order (n, L)).peak = UniformBatching.masterRootOrder n L ∧
    (run order (n, L)).valid := by
  obtain ⟨hv, hw, hp, hd⟩ := factor_spec L hL
  rw [order_bill, hv, hw]
  dsimp only
  have hfactor : 1 ≤ UniformBatching.rootFactor L := by
    unfold UniformBatching.rootFactor
    have h := pow_pos (by decide : 0 < (2 : ℕ)) (UniformBatching.rootBits L)
    omega
  have hpartial : 2 * n * L ≤ UniformBatching.masterRootOrder n L := by
    simpa only [UniformBatching.masterRootOrder, Nat.mul_one] using
      Nat.mul_le_mul_left (2 * n * L) hfactor
  have hnL : 2 * n ≤ 2 * n * L := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 * n) (show 1 ≤ L by omega)
  have h2 : 2 ≤ UniformBatching.masterRootOrder n L := by
    exact (show 2 ≤ 2 * n by omega).trans (hnL.trans hpartial)
  have h32 : 32 * L ≤ UniformBatching.masterRootOrder n L := by
    have h := Nat.mul_le_mul (show 2 ≤ 2 * n * L by omega)
      (UniformBatching.rootFactor_lower L)
    calc
      32 * L = 2 * (16 * L) := by ring
      _ ≤ UniformBatching.masterRootOrder n L := h
  have hpeak := hp.trans h32
  refine ⟨rfl, rfl, ?_, hd⟩
  change max (max (max 2 (2 * n)) (2 * n * L))
    (max (run factor L).peak (UniformBatching.masterRootOrder n L)) = _
  rw [max_eq_right hpeak]
  exact max_eq_right (max_le (max_le h2 (hnL.trans hpartial)) hpartial)

theorem work_le_actual_suffix (n L : ℕ) (hn : 0 < n) (hL : 0 < L) :
    (run order (n, L)).work ≤ 5 * (4 * UniformBatching.rootBits L + 12) := by
  rw [(order_spec n L hn hL).2.1]
  omega

/-- Exact agreement with the order actually requested by our master-root RAM. -/
theorem master_state_match {n : ℕ} (hn : 0 < n) {s : UniformMachine.State}
    (hs : UniformMasterRootMachine.MasterState n s) :
    (run order (n, UniformWorkingLength.workingLength n)).val = s.natReg 24 ∧
    (run order (n, UniformWorkingLength.workingLength n)).valid ∧
    (run order (n, UniformWorkingLength.workingLength n)).work ≤
      5 * UniformMasterRootMachine.preparationBudget n ∧
    (run order (n, UniformWorkingLength.workingLength n)).peak =
      UniformMasterRootMachine.order n := by
  have hL := UniformWorkingLength.workingLength_pos hn
  obtain ⟨hv, hw, hp, hd⟩ := order_spec n _ hn hL
  refine ⟨hv.trans hs.2.1.symm, hd, ?_, hp⟩
  have h := work_le_actual_suffix n _ hn hL
  unfold UniformMasterRootMachine.preparationBudget
  omega


theorem workingLength_one : UniformWorkingLength.workingLength 1 = 2 := by
  have hmax := (UniformWorkingLength.maximal_product (by decide : 0 < 1)).1
  have hodd := UniformWorkingLength.primeProduct_odd (UniformWorkingLength.axisCount 1)
  change Odd (UniformWorkingLength.oddProduct 1) at hodd
  obtain ⟨k, hk⟩ := hodd
  have hod : UniformWorkingLength.oddProduct 1 = 1 := by omega
  have he : UniformWorkingLength.doublingExponent 1 ≤ 1 :=
    Nat.find_min' (UniformWorkingLength.doubling_exists 1) (by rw [hod]; norm_num)
  have hlow := UniformWorkingLength.workingLength_lower 1
  have he0 : UniformWorkingLength.doublingExponent 1 ≠ 0 := by
    intro hz
    simp [UniformWorkingLength.workingLength, UniformWorkingLength.binaryFactor, hod, hz] at hlow
  have he1 : UniformWorkingLength.doublingExponent 1 = 1 := by omega
  simp [UniformWorkingLength.workingLength, UniformWorkingLength.binaryFactor, hod, he1]

theorem selected_order_one : UniformMasterRootMachine.order 1 = 128 := by
  rw [UniformMasterRootMachine.order, workingLength_one]
  norm_num [UniformBatching.masterRootOrder, UniformBatching.rootFactor, UniformBatching.rootBits]

theorem order_one :
    (run order (1, 2)).val = 128 ∧ (run order (1, 2)).valid ∧
    (run order (1, 2)).peak = 128 := by
  have h := order_spec 1 2 (by decide) (by decide)
  have hv : UniformBatching.masterRootOrder 1 2 = 128 := by
    simpa only [UniformMasterRootMachine.order, workingLength_one] using selected_order_one
  exact ⟨h.1.trans hv, h.2.2.2, h.2.2.1.trans hv⟩

end
end ExactFourierCircuits.DFTModelRoot

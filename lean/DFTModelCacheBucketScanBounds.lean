import DFTModelCacheBucketValues
import DFTModelCacheBucketStepBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheBucket
open OAI.PowerSaving OAI.PowerSaving.RAM
noncomputable section
attribute [local irreducible] step scan next selector

def selectBudget (G:ℕ):ℕ:=8+(G+1)*(89*G+29)
def selectPeak (N G:ℕ):ℕ:=N+(G+2)*(G+1)+1

private theorem gate_peak_arith (N c a j b:ℕ)
    (hc:c ≤ a+j) (hb:b ≤ max (N+1+j) (c+1)):
    b ≤ N+a+(j+1)+1 := by omega

private theorem level_peak_arith (N c G j b:ℕ)
    (hc:c ≤ j*G) (hb:b ≤ N+c+G+1):
    b ≤ N+(j+1+1)*(G+1)+1 := by nlinarith

theorem gateBill_count (x:Input.T) (l q:ℕ) (s:State.T) (j:ℕ):
    (gateBill x l q s j).val.1 ≤ s.1+j := by
  induction j with
  | zero=>simp [gateBill,Bill.steps,Bill.one]
  | succ j ih=>
    change (run step ((x,(l,q)),(j,(gateBill x l q s j).val))).val.1 ≤ _
    rw [step_value]
    have hh:=advance_count (depthValue x) l q j (gateBill x l q s j).val
    calc
      _ ≤ (gateBill x l q s j).val.1+1 := hh
      _ ≤ (s.1+j)+1 := Nat.add_le_add_right ih 1
      _ = s.1+(j+1) := Nat.add_assoc _ _ _

theorem gateBill_valid (x:Input.T) (l q:ℕ) (s:State.T) (j:ℕ):
    (gateBill x l q s j).valid := by
  induction j with
  | zero=>trivial
  | succ j ih=>
    change (gateBill x l q s j).valid ∧ (run step ((x,(l,q)),(j,(gateBill x l q s j).val))).valid
    exact ⟨ih,(step_bound _ _ _ _ _).1⟩

theorem gateBill_work (x:Input.T) (l q:ℕ) (s:State.T) (j:ℕ):
    (gateBill x l q s j).work ≤ 1+83*j := by
  induction j with
  | zero=>simp [gateBill,Bill.steps,Bill.one]
  | succ j ih=>
    have hh:=(step_bound x l q j (gateBill x l q s j).val).2.1
    change (gateBill x l q s j).work+(run step ((x,(l,q)),(j,(gateBill x l q s j).val))).work+1 ≤ _
    omega

theorem gateBill_peak (x:Input.T) (l q:ℕ) (s:State.T) (j:ℕ):
    (gateBill x l q s j).peak ≤ x.1+s.1+j+1 := by
  induction j with
  | zero=>exact Nat.zero_le _
  | succ j ih=>
    have hh:=(step_bound x l q j (gateBill x l q s j).val).2.2
    have hc:=gateBill_count x l q s j
    change max (max (gateBill x l q s j).peak
      (run step ((x,(l,q)),(j,(gateBill x l q s j).val))).peak) (j+1) ≤ _
    apply max_le
    · apply max_le
      · omega
      · exact gate_peak_arith x.1 _ s.1 j _ hc hh
    · omega

theorem scan_bound (x:Input.T) (l q:ℕ) (s:State.T):
    (run scan ((x,(l,q)),s)).valid ∧
    (run scan ((x,(l,q)),s)).work ≤ 89*x.2.1+10 ∧
    (run scan ((x,(l,q)),s)).peak ≤ x.1+s.1+x.2.1+1 := by
  have hw:=gateBill_work x l q s x.2.1
  have hp:=gateBill_peak x l q s x.2.1
  rw [scan_run]
  exact ⟨gateBill_valid _ _ _ _ _,by dsimp only [Bill.work];omega,hp⟩

theorem levelBill_count (x:Input.T) (L q j:ℕ):
    (levelBill x L q j).val.1 ≤ j*x.2.1 := by
  rw [levelBill_value]
  exact UniformDAGBucketMachine.offset_bound x.2.1 j (depthValue x)

theorem levelBill_valid (x:Input.T) (L q j:ℕ):
    (levelBill x L q j).valid := by
  induction j with
  | zero=>trivial
  | succ j ih=>
    change (levelBill x L q j).valid ∧ (run next ((x,(L,q)),(j,(levelBill x L q j).val))).valid
    rw [next_run]
    exact ⟨ih,(scan_bound _ _ _ _).1⟩

theorem levelBill_work (x:Input.T) (L q j:ℕ):
    (levelBill x L q j).work ≤ 1+j*(89*x.2.1+29) := by
  induction j with
  | zero=>simp [levelBill,Bill.steps,Bill.one]
  | succ j ih=>
    have hh:=(scan_bound x j q (levelBill x L q j).val).2.1
    change (levelBill x L q j).work+(run next ((x,(L,q)),(j,(levelBill x L q j).val))).work+1 ≤ _
    rw [next_run]
    dsimp only [Bill.pay]
    have he:(j+1)*(89*x.2.1+29)=j*(89*x.2.1+29)+(89*x.2.1+29):=by ring
    rw [he]
    omega

theorem levelBill_peak (x:Input.T) (L q j:ℕ):
    (levelBill x L q j).peak ≤ x.1+(j+1)*(x.2.1+1)+1 := by
  induction j with
  | zero=>exact Nat.zero_le _
  | succ j ih=>
    have hh:=(scan_bound x j q (levelBill x L q j).val).2.2
    have hc:=levelBill_count x L q j
    change max (max (levelBill x L q j).peak
      (run next ((x,(L,q)),(j,(levelBill x L q j).val))).peak) (j+1) ≤ _
    rw [next_run]
    dsimp only [Bill.pay]
    apply max_le
    · apply max_le
      · nlinarith
      · apply max_le
        · exact level_peak_arith x.1 _ x.2.1 j _ hc hh
        · omega
    · nlinarith

theorem selector_bound (x:Input.T) (L q:ℕ) (hL:L ≤ x.2.1+1):
    (run selector (x,(L,q))).valid ∧
    (run selector (x,(L,q))).work ≤ selectBudget x.2.1 ∧
    (run selector (x,(L,q))).peak ≤ selectPeak x.1 x.2.1 := by
  have hw:=levelBill_work x L q L
  have hp:=levelBill_peak x L q L
  rw [selector_run]
  dsimp only [Bill.work,Bill.peak,Bill.valid]
  refine ⟨levelBill_valid _ _ _ _,?_,?_⟩
  · unfold selectBudget
    nlinarith
  · unfold selectPeak
    nlinarith

end
end ExactFourierCircuits.DFTModelCacheBucket

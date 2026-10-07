import UniformWorkingMachine

set_option autoImplicit false

namespace ExactFourierCircuits.UniformWorkingCompletion
open UniformMachine
noncomputable section

/- The prefix halt becomes a charged jump to33. Added workspace:
   binary exponent=16, working length=17, binary factor=18.
   Constants and twice-n are explicitly initialized by charged instructions. -/
def suffix : Program :=
  [.natLiteral 12 2, .natLiteral 15 1, .natLiteral 9 0, .natBinary .mul 13 8 12,
   .natLiteral 16 0, .natLiteral 18 1, .natBinary .add 17 11 9,
   .branchLT 17 13 41 45, .natBinary .mul 18 18 12, .natBinary .mul 17 17 12,
   .natBinary .add 16 16 15, .jump 40, .halt]

def program : Program := UniformAssembly.embed [] UniformWorkingMachine.program suffix 33

theorem prefix_code : UniformAssembly.CodeAt UniformWorkingMachine.program program 0 33 :=
  UniformAssembly.embed_code [] UniformWorkingMachine.program suffix 33

theorem program_length : program.length = 46 := by decide

theorem suffix_code (i : ℕ) : program[33 + i]? = suffix[i]? := by
  simp [program, UniformAssembly.embed, UniformWorkingMachine.program_length,
    List.getElem?_append_right]

def Frame (s u : State) : Prop :=
  u.natHeap = s.natHeap ∧ u.scalarReg = s.scalarReg ∧ u.scalarHeap = s.scalarHeap ∧
    u.outputs = s.outputs ∧ u.rootOrders = s.rootOrders ∧
    ∀ r, r = 0 ∨ r = 8 ∨ r = 10 ∨ r = 11 ∨ 19 ≤ r → u.natReg r = s.natReg r

theorem frame_refl (s : State) : Frame s s := ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Frame.trans {s u v : State} (h : Frame s u) (h' : Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.1.trans h.2.2.2.1, h'.2.2.2.2.1.trans h.2.2.2.2.1,
    fun r hr => (h'.2.2.2.2.2 r hr).trans (h.2.2.2.2.2 r hr)⟩

def initialized (s : State) : State :=
  writeNat (writeNat (writeNat (writeNat (writeNat (writeNat (writeNat s 12 2) 15 1) 9 0)
    13 (2 * s.natReg 8)) 16 0) 18 1) 17 (s.natReg 11)

def Invariant (n e : ℕ) (s : State) : Prop :=
  s.pc = 40 ∧ s.natReg 12 = 2 ∧ s.natReg 15 = 1 ∧ s.natReg 13 = 2 * n ∧
    s.natReg 16 = e ∧ s.natReg 18 = 2 ^ e ∧
    s.natReg 17 = UniformWorkingLength.oddProduct n * 2 ^ e

def binaryState (s : State) : State := writeNat { s with pc := 41 } 18 (s.natReg 18 * 2)
def lengthState (s : State) : State := writeNat (binaryState s) 17 (s.natReg 17 * 2)
def exponentState (s : State) : State := writeNat (lengthState s) 16 (s.natReg 16 + 1)
def roundState (s : State) : State := { exponentState s with pc := 40 }

theorem phase_frames (s : State) : Frame s (initialized s) ∧ Frame s (roundState s) := by
  refine ⟨?_, ?_⟩
  all_goals refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  all_goals intro r hr
  all_goals have h9 : r ≠ 9 := by omega
  all_goals have h12 : r ≠ 12 := by omega
  all_goals have h13 : r ≠ 13 := by omega
  all_goals have h15 : r ≠ 15 := by omega
  all_goals have h16 : r ≠ 16 := by omega
  all_goals have h17 : r ≠ 17 := by omega
  all_goals have h18 : r ≠ 18 := by omega
  all_goals simp [initialized, roundState, exponentState, lengthState, binaryState, writeNat, next,
    h9, h12, h13, h15, h16, h17, h18]

theorem initializes_bounded (B n : ℕ) (x : Fin n → ℂ) (s : State)
    (hB : 46 ≤ B) (hnB : 4 * n ≤ B) (hsB : WordBound B s) (hp : s.pc = 33)
    (hn : s.natReg 8 = n) : BoundedRuns program n x B s 7 (initialized s) := by
  have h33 := suffix_code 0
  have h34 := suffix_code 1
  have h35 := suffix_code 2
  have h36 := suffix_code 3
  have h37 := suffix_code 4
  have h38 := suffix_code 5
  have h39 := suffix_code 6
  have h1 := writeNat_bound B s 12 2 hsB (by omega) (by omega)
  have h2 := writeNat_bound B (writeNat s 12 2) 15 1 h1
    (by simp [writeNat, next, hp]; omega) (by omega)
  have h3 := writeNat_bound B (writeNat (writeNat s 12 2) 15 1) 9 0 h2
    (by simp [writeNat, next, hp]; omega) (by omega)
  have h4 := writeNat_bound B (writeNat (writeNat (writeNat s 12 2) 15 1) 9 0) 13 (2 * s.natReg 8) h3
    (by simp [writeNat, next, hp]; omega) (by omega)
  have h5 := writeNat_bound B (writeNat (writeNat (writeNat (writeNat s 12 2) 15 1) 9 0)
    13 (2 * s.natReg 8)) 16 0 h4 (by simp [writeNat, next, hp]; omega) (by omega)
  have h6 := writeNat_bound B (writeNat (writeNat (writeNat (writeNat (writeNat s 12 2) 15 1)
    9 0) 13 (2 * s.natReg 8)) 16 0) 18 1 h5 (by simp [writeNat, next, hp]; omega) (by omega)
  have h7 := writeNat_bound B (writeNat (writeNat (writeNat (writeNat (writeNat (writeNat s 12 2) 15 1)
    9 0) 13 (2 * s.natReg 8)) 16 0) 18 1) 17 (s.natReg 11) h6
    (by simp [writeNat, next, hp]; omega) (hsB.2.1 11)
  refine .next hsB (u := writeNat s 12 2) ?_
    (.next h1 (u := writeNat (writeNat s 12 2) 15 1) ?_
      (.next h2 (u := writeNat (writeNat (writeNat s 12 2) 15 1) 9 0) ?_
        (.next h3 (u := writeNat (writeNat (writeNat (writeNat s 12 2) 15 1) 9 0) 13 (2 * s.natReg 8)) ?_
          (.next h4 (u := writeNat (writeNat (writeNat (writeNat (writeNat s 12 2) 15 1) 9 0)
            13 (2 * s.natReg 8)) 16 0) ?_
            (.next h5 (u := writeNat (writeNat (writeNat (writeNat (writeNat (writeNat s 12 2) 15 1)
              9 0) 13 (2 * s.natReg 8)) 16 0) 18 1) ?_
              (.next h6 (u := initialized s) ?_ (.refl h7)))))))
  all_goals simp [step, evalNat, initialized, writeNat, next, hp, suffix,
    h33, h34, h35, h36, h37, h38, h39, Nat.mul_comm]

theorem initialized_invariant (n : ℕ) (s : State) (hp : s.pc = 33)
    (hn : s.natReg 8 = n) (hR : s.natReg 11 = UniformWorkingLength.oddProduct n) :
    Invariant n 0 (initialized s) := by
  simp [Invariant, initialized, writeNat, next, hp, hn, hR]

theorem round_invariant (n e : ℕ) (s : State) (hs : Invariant n e s) :
    Invariant n (e + 1) (roundState s) := by
  obtain ⟨_, h12, h15, h13, he, hbin, hlen⟩ := hs
  simp [Invariant, roundState, exponentState, lengthState, binaryState, writeNat, next,
    h12, h15, h13, he, hbin, hlen, pow_succ, Nat.mul_assoc]

theorem round_bounded (B n e : ℕ) (x : Fin n → ℂ) (s : State)
    (hB : 46 ≤ B) (hnB : 4 * n ≤ B) (hs : Invariant n e s) (hb : WordBound B s)
    (hgo : s.natReg 17 < 2 * n) : BoundedRuns program n x B s 5 (roundState s) := by
  obtain ⟨hp, h12, h15, h13, he, hbin, hlen⟩ := hs
  have hR := UniformWorkingLength.oddProduct_pos n
  have hbinlen : s.natReg 18 ≤ s.natReg 17 := by rw [hbin, hlen]; nlinarith
  have hep : e < 2 ^ e := Nat.lt_pow_self (by decide)
  have hbinB : s.natReg 18 * 2 ≤ B := by omega
  have hlenB : s.natReg 17 * 2 ≤ B := by omega
  have heB : s.natReg 16 + 1 ≤ B := by omega
  have h41 := changePC_bound B s 41 hb (by omega)
  have h42 := writeNat_bound B { s with pc := 41 } 18 (s.natReg 18 * 2) h41 (by simp; omega) hbinB
  have h43 := writeNat_bound B (binaryState s) 17 (s.natReg 17 * 2) h42
    (by simp [binaryState, writeNat, next]; omega) hlenB
  have h44 := writeNat_bound B (lengthState s) 16 (s.natReg 16 + 1) h43
    (by simp [lengthState, binaryState, writeNat, next]; omega) heB
  have h40 := changePC_bound B _ 40 h44 (by omega)
  have hc40 := suffix_code 7
  have hc41 := suffix_code 8
  have hc42 := suffix_code 9
  have hc43 := suffix_code 10
  have hc44 := suffix_code 11
  refine .next hb (u := { s with pc := 41 }) ?_
    (.next h41 (u := binaryState s) ?_ (.next h42 (u := lengthState s) ?_
      (.next h43 (u := exponentState s) ?_ (.next h44 (u := roundState s) ?_ (.refl h40)))))
  all_goals simp [step, evalNat, roundState, exponentState, lengthState, binaryState,
    writeNat, next, hp, h12, h15, h13, hgo, suffix, hc40, hc41, hc42, hc43, hc44]

/-- The proof-only induction parameter is absent from the program. The loop doubles
    until its actual integer guard first becomes false. -/
theorem doubling_bounded (B n : ℕ) (x : Fin n → ℂ) (fuel e : ℕ) (s : State)
    (hB : 46 ≤ B) (hnB : 4 * n ≤ B)
    (he : e ≤ UniformWorkingLength.doublingExponent n)
    (hf : UniformWorkingLength.doublingExponent n - e + 1 ≤ fuel)
    (hs : Invariant n e s) (hb : WordBound B s) : ∃ u,
    BoundedExecution program n x B s (5 * (UniformWorkingLength.doublingExponent n - e) + 2) u ∧
      u.pc = 45 ∧ u.natReg 16 = UniformWorkingLength.doublingExponent n ∧
      u.natReg 18 = UniformWorkingLength.binaryFactor n ∧
      u.natReg 17 = UniformWorkingLength.workingLength n ∧ Frame s u := by
  induction fuel generalizing e s with
  | zero => omega
  | succ fuel ih =>
    by_cases hend : e = UniformWorkingLength.doublingExponent n
    · obtain ⟨hp, _, _, h13, h16, h18, h17⟩ := hs
      have hstop : ¬s.natReg 17 < s.natReg 13 := by
        rw [h13, h17, hend]
        exact Nat.not_lt.mpr (UniformWorkingLength.workingLength_lower n)
      let u := { s with pc := 45 }
      refine ⟨u, ?_, rfl, h16.trans hend, ?_, ?_, frame_refl s⟩
      · rw [hend, Nat.sub_self]
        refine .next hb (u := u) ?_ (.halt (changePC_bound B s 45 hb (by omega)) ?_)
        · simp [step, hp, suffix_code 7, suffix, hstop, u]
        · simp [step, suffix_code 12, suffix, u]
      · simpa [UniformWorkingLength.binaryFactor, hend] using h18
      · simpa [UniformWorkingLength.workingLength, UniformWorkingLength.binaryFactor, hend] using h17
    · have hlt : e < UniformWorkingLength.doublingExponent n := by omega
      have hgo : s.natReg 17 < 2 * n := by
        rw [hs.2.2.2.2.2.2]
        exact UniformWorkingLength.doubling_minimal n e hlt
      have hr := round_bounded B n e x s hB hnB hs hb hgo
      obtain ⟨u, hu, hp, h16, h18, h17, hframe⟩ := ih (e + 1) (roundState s)
        (by omega) (by omega) (round_invariant n e s hs) hr.final_bound
      refine ⟨u, ?_, hp, h16, h18, h17, (phase_frames s).2.trans hframe⟩
      have hrun := hr.executes hu
      convert hrun using 1; omega

theorem wordBound_setup {n : ℕ} (hn : 0 < n) : 46 ≤ (n + 2) ^ 9 ∧ 4 * n ≤ (n + 2) ^ 9 := by
  have hpow : 6561 ≤ (n + 2) ^ 8 := by
    have h := Nat.pow_le_pow_left (show 3 ≤ n + 2 by omega) 8
    norm_num at h
    exact h
  have hm := Nat.mul_le_mul_left (n + 2) hpow
  have hl : 4 * n + 46 ≤ (n + 2) * 6561 := by omega
  have hbound : 4 * n + 46 ≤ (n + 2) ^ 9 := by
    calc
      4 * n + 46 ≤ (n + 2) * 6561 := hl
      _ ≤ (n + 2) * (n + 2) ^ 8 := hm
      _ = (n + 2) ^ 9 := by simpa [Nat.mul_comm] using (pow_succ (n + 2) 8).symm
  omega

def PreparedState (n : ℕ) (u : State) : Prop :=
  UniformWorkingMachine.SelectedState n u ∧
    u.natReg 16 = UniformWorkingLength.doublingExponent n ∧
    u.natReg 18 = UniformWorkingLength.binaryFactor n ∧
    u.natReg 17 = UniformWorkingLength.workingLength n

theorem Frame.selected {n : ℕ} {s u : State} (hf : Frame s u)
    (hs : UniformWorkingMachine.SelectedState n s) : UniformWorkingMachine.SelectedState n u := by
  obtain ⟨h0, h10, h11, ht, hh⟩ := hs
  refine ⟨(hf.2.2.2.2.2 0 (by simp)).trans h0,
    (hf.2.2.2.2.2 10 (by simp)).trans h10,
    (hf.2.2.2.2.2 11 (by simp)).trans h11, ?_, ?_⟩
  · simpa [UniformWorkingMachine.PrimeTable, hf.1] using ht
  · simpa [hf.1] using hh

theorem completion_cost_bound {n : ℕ} (hn : 0 < n) :
    30000 * (UniformWorkingLength.axisCount n + 2) ^ 4 +
      5 * UniformWorkingLength.doublingExponent n + 9 ≤
        40000 * (UniformWorkingLength.axisCount n + 2) ^ 4 := by
  have he : UniformWorkingLength.doublingExponent n < UniformWorkingLength.binaryFactor n :=
    Nat.lt_pow_self (by decide)
  have hb := UniformWorkingLength.binaryFactor_quadratic hn
  have ha : 4 ≤ (UniformWorkingLength.axisCount n + 2) ^ 2 :=
    Nat.pow_le_pow_left (show 2 ≤ UniformWorkingLength.axisCount n + 2 by omega) 2
  have hsq : (UniformWorkingLength.axisCount n + 2) ^ 4 =
      ((UniformWorkingLength.axisCount n + 2) ^ 2) ^ 2 := by rw [← pow_mul]
  rw [hsq]
  nlinarith

/-- One literal fixed program performs prime selection/table writes followed by the
    minimal doubling loop. Every transition, including the phase jump, is charged. -/
theorem preparation_execution {n : ℕ} (hn : 0 < n) (x : Fin n → ℂ) : ∃ t u,
    BoundedExecution program n x ((n + 2) ^ 9) initial t u ∧ PreparedState n u ∧
      u.pc = 45 ∧ u.natReg 8 = n ∧
      u.scalarReg = initial.scalarReg ∧ u.scalarHeap = initial.scalarHeap ∧
      u.outputs = initial.outputs ∧ u.rootOrders = [] ∧
      t ≤ 40000 * (UniformWorkingLength.axisCount n + 2) ^ 4 := by
  obtain ⟨hB, hnB⟩ := wordBound_setup hn
  obtain ⟨t, v, hv, _, h8, h0, h10, h11, htab, hheap, hs, hh, ho, hd, hc⟩ :=
    UniformWorkingMachine.prefix_execution hn x
  have hvBound := UniformWorkingMachine.boundedExecution_mono
    (UniformWorkingMachine.wordBound_polynomial hn) hv
  have hprefix : BoundedRuns program n x ((n + 2) ^ 9) initial t { v with pc := 33 } := by
    have hp := UniformAssembly.BoundedExecution.placed prefix_code
      (by omega : 0 + (n + 2) ^ 9 ≤ (n + 2) ^ 9) (by omega : 33 ≤ (n + 2) ^ 9) hvBound
    simpa [UniformAssembly.placed, initial] using hp
  let entry := { v with pc := 33 }
  have hinit := initializes_bounded ((n + 2) ^ 9) n x entry hB hnB hprefix.final_bound rfl h8
  obtain ⟨u, hu, hp, h16, h18, h17, hf⟩ := doubling_bounded ((n + 2) ^ 9) n x
    (UniformWorkingLength.doublingExponent n + 1) 0 (initialized entry) hB hnB
    (by omega) (by omega) (initialized_invariant n entry rfl h8 h11) hinit.final_bound
  have hframe : Frame entry u := (phase_frames entry).1.trans hf
  have hselected : UniformWorkingMachine.SelectedState n entry := ⟨h0, h10, h11, htab, hheap⟩
  refine ⟨t + 7 + (5 * UniformWorkingLength.doublingExponent n + 2), u, ?_,
    ⟨hframe.selected hselected, h16, h18, h17⟩, hp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.sub_zero] using (hprefix.trans hinit).executes hu
  · exact (hframe.2.2.2.2.2 8 (by simp)).trans h8
  · exact hframe.2.1.trans hs
  · exact hframe.2.2.1.trans hh
  · exact hframe.2.2.2.1.trans ho
  · exact hframe.2.2.2.2.1.trans hd
  · have hpcost := hc.trans (UniformWorkingMachine.prefix_cost_polynomial hn)
    have htotal := completion_cost_bound hn
    omega

theorem minimal_binary_width {n : ℕ} {u : State} (hu : PreparedState n u) :
    ∀ e, e < u.natReg 16 → UniformWorkingLength.oddProduct n * 2 ^ e < 2 * n := by
  intro e he
  rw [hu.2.1] at he
  exact UniformWorkingLength.doubling_minimal n e he

theorem working_length_bounds {n : ℕ} (hn : 0 < n) {u : State} (hu : PreparedState n u) :
    2 * n ≤ u.natReg 17 ∧ u.natReg 17 < 4 * n := by
  rw [hu.2.2.2]
  exact ⟨UniformWorkingLength.workingLength_lower n, UniformWorkingLength.workingLength_upper hn⟩

def preparationBudget (n : ℕ) : ℕ := 40000 * (UniformWorkingLength.axisCount n + 2) ^ 4

/-- The actual execution budget is sublinear in the input length. -/
theorem preparationBudget_isLittleO_input :
    (fun n : ℕ => (preparationBudget n : ℝ)) =o[Filter.atTop] (fun n : ℕ => (n : ℝ)) := by
  have hbudget : (fun n : ℕ => (preparationBudget n : ℝ)) =O[Filter.atTop]
      (fun n : ℕ => ((UniformWorkingLength.axisCount n + 2 : ℕ) : ℝ) ^ 4) := by
    apply Asymptotics.IsBigO.of_bound 40000
    filter_upwards [] with n
    simp [preparationBudget]
  have hlog := hbudget.trans (UniformWorkingPreparation.axisCount_plus_two_isBigO_log.pow 4)
  have hlittle : (fun n : ℕ => Real.log (n : ℝ) ^ 4) =o[Filter.atTop] (fun n : ℕ => (n : ℝ)) :=
    Real.isLittleO_pow_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  exact hlog.trans_isLittleO hlittle

end
end ExactFourierCircuits.UniformWorkingCompletion

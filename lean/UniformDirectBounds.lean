import UniformDirectMachine

set_option autoImplicit false

namespace ExactFourierCircuits.UniformDirectBounds
open UniformMachine UniformDirectMachine
noncomputable section

/-- The loop counters are bounded even at the two increment instructions.
    Strict bounds are needed only inside their respective loop bodies. -/
def Counters (n : ℕ) (s : State) : Prop :=
  5 ≤ s.pc ∧ s.pc ≤ 20 ∧ s.natReg 0 = n ∧ s.natReg 3 = 1 ∧
    s.natReg 1 ≤ n ∧ s.natReg 2 ≤ n ∧
    (6 ≤ s.pc → s.pc ≤ 18 → s.natReg 1 < n) ∧
    (10 ≤ s.pc → s.pc ≤ 14 → s.natReg 2 < n)

def Interior (n : ℕ) (s : State) : Prop := WordBound (n + 21) s ∧ Counters n s

theorem step_interior (n : ℕ) (x : Fin n → ℂ) (s u : State)
    (hs : Interior n s) (h : step program n x s = .running u) : Interior n u := by
  obtain ⟨hb, hlo, hhi, hn, hone, hk, hj, hkstrict, hjstrict⟩ := hs
  have hpnext : s.pc + 1 ≤ n + 21 := by omega
  have hscalar (dst : ℕ) (v : Scalar) : WordBound (n + 21) (writeScalar s dst v) :=
    writeScalar_bound _ s dst v hb hpnext
  interval_cases hpc : s.pc
  · by_cases hkn : s.natReg 1 < n
    · simp [step, program, hpc, hn, hkn] at h
      subst u
      refine ⟨changePC_bound _ s 6 hb (by omega), ?_⟩
      simp only [Counters]; omega
    · simp [step, program, hpc, hn, hkn] at h
      subst u
      refine ⟨changePC_bound _ s 20 hb (by omega), ?_⟩
      simp only [Counters]; omega
  · simp [step, program, hpc] at h
    subst u
    refine ⟨writeNat_bound _ s 2 0 hb (by omega) (by omega), ?_⟩
    simp only [Counters, writeNat, next, Function.update_self, Function.update_of_ne
      (by decide : (0 : ℕ) ≠ 2), Function.update_of_ne (by decide : (1 : ℕ) ≠ 2),
      Function.update_of_ne (by decide : (3 : ℕ) ≠ 2)]
    omega
  · simp [step, program, hpc] at h
    subst u
    refine ⟨hscalar 2 _, ?_⟩
    simp only [Counters, writeScalar, next]; omega
  · simp [step, program, hpc] at h
    subst u
    refine ⟨hscalar 3 _, ?_⟩
    simp only [Counters, writeScalar, next]; omega
  · by_cases hjn : s.natReg 2 < n
    · simp [step, program, hpc, hn, hjn] at h
      subst u
      refine ⟨changePC_bound _ s 10 hb (by omega), ?_⟩
      simp only [Counters]; omega
    · simp [step, program, hpc, hn, hjn] at h
      subst u
      refine ⟨changePC_bound _ s 16 hb (by omega), ?_⟩
      simp only [Counters]; omega
  · have hjn : s.natReg 2 < n := hjstrict (by omega) (by omega)
    simp [step, program, hpc, hjn] at h
    subst u
    refine ⟨hscalar 4 _, ?_⟩
    simp only [Counters, writeScalar, next]; omega
  · obtain ⟨v, rfl⟩ := field_step_write (dst := 5) (left := 2) (right := 4) (op := .mul) (by simp [program, hpc]) h
    refine ⟨hscalar 5 v, ?_⟩
    simp only [Counters, writeScalar, next]; omega
  · obtain ⟨v, rfl⟩ := field_step_write (dst := 3) (left := 3) (right := 5) (op := .add) (by simp [program, hpc]) h
    refine ⟨hscalar 3 v, ?_⟩
    simp only [Counters, writeScalar, next]; omega
  · obtain ⟨v, rfl⟩ := field_step_write (dst := 2) (left := 2) (right := 1) (op := .mul) (by simp [program, hpc]) h
    refine ⟨hscalar 2 v, ?_⟩
    simp only [Counters, writeScalar, next]; omega
  · have hjn : s.natReg 2 < n := hjstrict (by omega) (by omega)
    simp [step, program, hpc, evalNat, hone] at h
    subst u
    refine ⟨writeNat_bound _ s 2 (s.natReg 2 + 1) hb (by omega) (by omega), ?_⟩
    simp only [Counters, writeNat, next, Function.update_self, Function.update_of_ne
      (by decide : (0 : ℕ) ≠ 2), Function.update_of_ne (by decide : (1 : ℕ) ≠ 2),
      Function.update_of_ne (by decide : (3 : ℕ) ≠ 2)]
    omega
  · simp [step, program, hpc] at h
    subst u
    refine ⟨changePC_bound _ s 9 hb (by omega), ?_⟩
    simp only [Counters]; omega
  · have hkn : s.natReg 1 < n := hkstrict (by omega) (by omega)
    simp [step, program, hpc, hkn] at h
    subst u
    refine ⟨emit_bound _ s (s.natReg 1) _ (s.pc + 1) hb (by omega) (by omega), ?_⟩
    simp only [Counters, next]; omega
  · obtain ⟨v, rfl⟩ := field_step_write (dst := 1) (left := 1) (right := 0) (op := .mul) (by simp [program, hpc]) h
    refine ⟨hscalar 1 v, ?_⟩
    simp only [Counters, writeScalar, next]; omega
  · have hkn : s.natReg 1 < n := hkstrict (by omega) (by omega)
    simp [step, program, hpc, evalNat, hone] at h
    subst u
    refine ⟨writeNat_bound _ s 1 (s.natReg 1 + 1) hb (by omega) (by omega), ?_⟩
    simp only [Counters, writeNat, next, Function.update_self, Function.update_of_ne
      (by decide : (0 : ℕ) ≠ 1), Function.update_of_ne (by decide : (2 : ℕ) ≠ 1),
      Function.update_of_ne (by decide : (3 : ℕ) ≠ 1)]
    omega
  · simp [step, program, hpc] at h
    subst u
    refine ⟨changePC_bound _ s 5 hb (by omega), ?_⟩
    simp only [Counters]; omega
  · simp [step, program, hpc] at h

theorem startupRoot_bound (n : ℕ) : WordBound (n + 21) (startupRoot n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [startupRoot, writeScalar, writeNat, next, initial]
  · intro r
    by_cases h0 : r = 0 <;> by_cases h3 : r = 3 <;>
      simp [startupRoot, writeScalar, writeNat, next, initial, h0, h3]
  · simp [startupRoot, writeScalar, writeNat, next, initial]
  · simp [startupRoot, writeScalar, writeNat, next, initial]
  · simp [startupRoot, writeScalar, writeNat, next, initial]
  · simp [startupRoot, writeScalar, writeNat, next, initial]

theorem startup_bounded {n : ℕ} (hn : 0 < n) (x : Fin n → ℂ) :
    BoundedRuns program n x (n + 21) initial 5 (startup n) := by
  have h0 := initial_wordBound (n + 21)
  have h1 : WordBound (n + 21) (writeNat initial 0 n) :=
    writeNat_bound _ initial 0 n h0 (by simp [initial]) (by omega)
  have h2 : WordBound (n + 21) (writeNat (writeNat initial 0 n) 3 1) :=
    writeNat_bound _ _ 3 1 h1 (by simp [writeNat, next, initial]) (by omega)
  have h3 := startupRoot_bound n
  have h4 : WordBound (n + 21) (writeNat (startupRoot n) 1 0) :=
    writeNat_bound _ _ 1 0 h3 (by simp [startupRoot, writeScalar, writeNat, next, initial]) (by omega)
  have h5 : WordBound (n + 21) (startup n) :=
    writeScalar_bound _ _ 1 ⟨1, false⟩ h4
      (by simp [startupRoot, writeScalar, writeNat, next, initial])
  refine .next h0 ?_ (.next h1 ?_ (.next h2 ?_ (.next h3 ?_ (.next h4 ?_ (.refl h5)))))
  all_goals simp [step, program, initial, writeNat, writeScalar, next, startupRoot, startup, hn.ne']

theorem startup_counters (n : ℕ) : Counters n (startup n) := by
  simp [Counters, startup, startupRoot, writeNat, writeScalar, next, initial]

/-- The literal direct DFT fallback has a linear bound on every intermediate
    integer and heap/output address, including its charged initialization. -/
theorem direct_bounded {n : ℕ} (hn : 0 < n) (x : Fin n → ℂ) : ∃ s : State,
    BoundedExecution program n x (n + 21) initial (7 * n ^ 2 + 9 * n + 7) s ∧
      ComputesDFT n x s ∧ s.rootOrders = [n] := by
  obtain ⟨s, hr, hi⟩ := outer_loop x n 0 (startup n) (by omega) (startup_invariant x)
  have hstart := startup_bounded hn x
  have hs : Interior n (startup n) := ⟨hstart.final_bound, startup_counters n⟩
  have hex := hr.executes (halt_executes x s hi)
  have hb := hex.bounded_of_invariant (Interior n) hs
    (fun _ h => h.1) (fun s u h => step_interior n x s u h)
  refine ⟨{ s with pc := 20 }, ?_, ?_, hi.1.2.2.2.2.2⟩
  · convert hstart.executes hb using 1; ring
  · intro j
    exact hi.2.2 j j.isLt

theorem wordBound_mono {B C : ℕ} (h : B ≤ C) {s : State} (hs : WordBound B s) :
    WordBound C s := by
  obtain ⟨hp, hr, hn, hc, ho, hd⟩ := hs
  exact ⟨hp.trans h, fun r => (hr r).trans h,
    fun a v hv => ⟨(hn a v hv).1.trans h, (hn a v hv).2.trans h⟩,
    fun a v hv => (hc a v hv).trans h, fun a v hv => (ho a v hv).trans h,
    fun d hd' => (hd d hd').trans h⟩

theorem boundedExecution_mono {p : Program} {n B C t : ℕ} {x : Fin n → ℂ}
    {s u : State} (h : B ≤ C) (hx : BoundedExecution p n x B s t u) :
    BoundedExecution p n x C s t u := by
  induction hx with
  | halt hb hh => exact .halt (wordBound_mono h hb) hh
  | next hb hh _ ih => exact .next (wordBound_mono h hb) hh ih

theorem linear_le_polynomial {n : ℕ} (hn : 0 < n) : n + 21 ≤ (n + 2) ^ 5 := by
  have h81 : 81 ≤ (n + 2) ^ 4 :=
    Nat.pow_le_pow_left (by omega : 3 ≤ n + 2) 4
  calc
    n + 21 ≤ 81 * (n + 2) := by omega
    _ ≤ (n + 2) ^ 4 * (n + 2) := Nat.mul_le_mul_right _ h81
    _ = (n + 2) ^ 5 := (pow_succ (n + 2) 4).symm

/-- The same actual fallback execution also meets a fixed polynomial word bound. -/
theorem direct_polynomial_bounded {n : ℕ} (hn : 0 < n) (x : Fin n → ℂ) : ∃ s : State,
    BoundedExecution program n x ((n + 2) ^ 5) initial (7 * n ^ 2 + 9 * n + 7) s ∧
      ComputesDFT n x s ∧ s.rootOrders = [n] := by
  obtain ⟨s, hs, hdft, hroots⟩ := direct_bounded hn x
  exact ⟨s, boundedExecution_mono (linear_le_polynomial hn) hs, hdft, hroots⟩

end
end ExactFourierCircuits.UniformDirectBounds

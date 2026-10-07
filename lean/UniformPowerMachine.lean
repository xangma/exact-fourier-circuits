import UniformMachineRuns
import UniformRoots

set_option autoImplicit false

namespace ExactFourierCircuits.UniformPowerMachine
open UniformMachine
noncomputable section

/- Nat registers: exponent=0, zero=1, one=2, two=3, parity=4.
   Scalar registers: accumulator=0, prepared base=1. -/
def program : Program :=
  [.natLiteral 1 0, .natLiteral 2 1, .natLiteral 3 2, .scalarLiteral 0 1,
   .branchLT 1 0 5 11, .natBinary .mod 4 0 3, .branchLT 1 4 7 8,
   .fieldBinary .mul 0 0 1, .fieldBinary .mul 1 1 1,
   .natBinary .div 0 0 3, .jump 4, .halt]

def initialized (s : State) : State :=
  writeScalar (writeNat (writeNat (writeNat s 1 0) 2 1) 3 2) 0 ⟨1, false⟩

def LoopInvariant (s : State) : Prop :=
  s.pc = 4 ∧ s.natReg 1 = 0 ∧ s.natReg 2 = 1 ∧ s.natReg 3 = 2 ∧
    (s.scalarReg 0).dependent = false ∧ (s.scalarReg 1).dependent = false

def entered (s : State) : State := { s with pc := 5 }
def parityState (s : State) : State := writeNat (entered s) 4 (s.natReg 0 % 2)
def accumulatorState (s : State) : State :=
  if s.natReg 0 % 2 = 0 then { parityState s with pc := 8 }
  else writeScalar { parityState s with pc := 7 } 0
    ⟨(s.scalarReg 0).value * (s.scalarReg 1).value, false⟩
def squaredState (s : State) : State := writeScalar (accumulatorState s) 1
  ⟨(s.scalarReg 1).value * (s.scalarReg 1).value, false⟩
def halfState (s : State) : State := writeNat (squaredState s) 0 (s.natReg 0 / 2)
def roundState (s : State) : State := { halfState s with pc := 4 }
def roundCost (e : ℕ) : ℕ := if e % 2 = 0 then 6 else 7

def iterations (e : ℕ) : ℕ := if h : e = 0 then 0 else iterations (e / 2) + 1
termination_by e
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

def loopCost (e : ℕ) : ℕ := if _h : e = 0 then 2 else loopCost (e / 2) + roundCost e
termination_by e
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

theorem iterations_zero : iterations 0 = 0 := by rw [iterations]; rfl
theorem iterations_step (e : ℕ) (he : e ≠ 0) : iterations e = iterations (e / 2) + 1 := by
  rw [iterations, dite_eq_right he]
theorem loopCost_zero : loopCost 0 = 2 := by rw [loopCost]; rfl
theorem loopCost_step (e : ℕ) (he : e ≠ 0) : loopCost e = loopCost (e / 2) + roundCost e := by
  rw [loopCost, dite_eq_right he]

theorem iterations_log (e : ℕ) : iterations e = if e = 0 then 0 else Nat.log2 e + 1 := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases he : e = 0
    · subst e; rw [iterations_zero]; rfl
    · rw [iterations_step e he, ite_eq_right he]
      by_cases hsmall : e < 2
      · have heq : e = 1 := by omega
        subst e
        rw [show 1 / 2 = 0 from rfl, iterations_zero]
        rfl
      · have hpos : 0 < e / 2 := Nat.div_pos (by omega) (by decide)
        rw [ih (e / 2) (Nat.div_lt_self (by omega) (by decide)), ite_eq_right hpos.ne']
        conv_rhs => rw [Nat.log2_def, ite_eq_left (by omega : 2 ≤ e)]

theorem loopCost_iterations (e : ℕ) : loopCost e ≤ 7 * iterations e + 2 := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases he : e = 0
    · subst e; simp [loopCost_zero, iterations_zero]
    · have ht := ih (e / 2) (Nat.div_lt_self (by omega) (by decide))
      have hr : roundCost e ≤ 7 := by unfold roundCost; split <;> omega
      rw [loopCost_step e he, iterations_step e he]
      omega

theorem iterations_log_succ_bound (e : ℕ) : iterations e ≤ Nat.log2 (e + 1) + 1 := by
  rw [iterations_log]
  split
  · omega
  · rename_i he
    have hm : Nat.log2 e ≤ Nat.log2 (e + 1) :=
      (Nat.le_log2 (by omega : e + 1 ≠ 0)).2 ((Nat.log2_self_le he).trans (by omega))
    omega

theorem totalCost_log_bound (e : ℕ) : 4 + loopCost e ≤ 7 * (Nat.log2 (e + 1) + 1) + 6 := by
  have hc := loopCost_iterations e
  have hi := iterations_log_succ_bound e
  omega

theorem initializes (s : State) (hpc : s.pc = 0) (n : ℕ) (x : Fin n → ℂ) :
    Runs program n x s 4 (initialized s) := by
  refine .next (u := writeNat s 1 0) ?_ (.next (u := writeNat (writeNat s 1 0) 2 1) ?_
    (.next (u := writeNat (writeNat (writeNat s 1 0) 2 1) 3 2) ?_
      (.next (u := initialized s) ?_ (.refl _))))
  all_goals simp [step, program, initialized, writeNat, writeScalar, next, hpc]

theorem initialized_invariant (s : State) (hpc : s.pc = 0) (hb : (s.scalarReg 1).dependent = false) :
    LoopInvariant (initialized s) := by
  simp [LoopInvariant, initialized, writeNat, writeScalar, next, hpc, hb]

theorem round_invariant (s : State) (hs : LoopInvariant s) : LoopInvariant (roundState s) := by
  obtain ⟨hpc, hzero, hone, htwo, hacc, hbase⟩ := hs
  by_cases he : s.natReg 0 % 2 = 0 <;>
    simp [LoopInvariant, roundState, halfState, squaredState, accumulatorState,
      parityState, entered, writeNat, writeScalar, next, he, hzero, hone, htwo, hacc]

theorem round_exponent (s : State) : (roundState s).natReg 0 = s.natReg 0 / 2 := by
  simp [roundState, halfState, writeNat]

theorem round_values (s : State) :
    (roundState s).scalarReg 0 =
      (if s.natReg 0 % 2 = 0 then s.scalarReg 0 else
        ⟨(s.scalarReg 0).value * (s.scalarReg 1).value, false⟩) ∧
      (roundState s).scalarReg 1 = ⟨(s.scalarReg 1).value * (s.scalarReg 1).value, false⟩ := by
  by_cases he : s.natReg 0 % 2 = 0 <;>
    simp [roundState, halfState, squaredState, accumulatorState, parityState, entered,
      writeNat, writeScalar, next, he]

theorem square_pow (b : ℂ) (e : ℕ) : (b * b) ^ e = b ^ (2 * e) := by
  rw [← pow_two, ← pow_mul]

theorem round_power_invariant (s : State) :
    ((roundState s).scalarReg 0).value * ((roundState s).scalarReg 1).value ^ (roundState s).natReg 0 =
      (s.scalarReg 0).value * (s.scalarReg 1).value ^ s.natReg 0 := by
  obtain ⟨ha, hb⟩ := round_values s
  rw [round_exponent, ha, hb]
  have hm := Nat.mod_lt (s.natReg 0) (by decide : 0 < 2)
  have heq := Nat.div_add_mod (s.natReg 0) 2
  by_cases he : s.natReg 0 % 2 = 0
  · rw [ite_eq_left he, square_pow]
    have hx : 2 * (s.natReg 0 / 2) = s.natReg 0 := by omega
    rw [hx]
  · rw [ite_eq_right he]
    change ((s.scalarReg 0).value * (s.scalarReg 1).value) *
      ((s.scalarReg 1).value * (s.scalarReg 1).value) ^ (s.natReg 0 / 2) = _
    rw [square_pow]
    have hx : s.natReg 0 = 2 * (s.natReg 0 / 2) + 1 := by omega
    conv_rhs => rw [hx, pow_succ]
    ring

theorem round_runs (s : State) (hs : LoopInvariant s) (he : 0 < s.natReg 0)
    (n : ℕ) (x : Fin n → ℂ) : Runs program n x s (roundCost (s.natReg 0)) (roundState s) := by
  obtain ⟨hpc, hzero, hone, htwo, hacc, hbase⟩ := hs
  by_cases hm : s.natReg 0 % 2 = 0
  · rw [roundCost, ite_eq_left hm]
    refine .next (u := entered s) ?_ (.next (u := parityState s) ?_
      (.next (u := { parityState s with pc := 8 }) ?_ (.next (u := squaredState s) ?_
        (.next (u := halfState s) ?_ (.next (u := roundState s) ?_ (.refl _))))))
    all_goals simp [step, program, evalNat, evalField, roundState, halfState, squaredState,
      accumulatorState, parityState, entered, writeNat, writeScalar, next,
      hpc, hzero, htwo, hbase, hm, he]
  · have hmpos : 0 < s.natReg 0 % 2 := Nat.pos_of_ne_zero hm
    rw [roundCost, ite_eq_right hm]
    refine .next (u := entered s) ?_ (.next (u := parityState s) ?_
      (.next (u := { parityState s with pc := 7 }) ?_ (.next (u := accumulatorState s) ?_
        (.next (u := squaredState s) ?_ (.next (u := halfState s) ?_
          (.next (u := roundState s) ?_ (.refl _)))))))
    all_goals simp [step, program, evalNat, evalField, roundState, halfState, squaredState,
      accumulatorState, parityState, entered, writeNat, writeScalar, next,
      hpc, hzero, htwo, hacc, hbase, hm, he, hmpos]

def Frame (s u : State) : Prop :=
  u.natHeap = s.natHeap ∧ u.scalarHeap = s.scalarHeap ∧ u.outputs = s.outputs ∧
    u.rootOrders = s.rootOrders ∧ (∀ r, 5 ≤ r → u.natReg r = s.natReg r) ∧
      (∀ r, r ≠ 0 → r ≠ 1 → u.scalarReg r = s.scalarReg r)

theorem frame_refl (s : State) : Frame s s := by
  exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem Frame.trans {s u v : State} (h : Frame s u) (h' : Frame u v) : Frame s v := by
  obtain ⟨hn, hc, ho, hr, hi, hf⟩ := h
  obtain ⟨hn', hc', ho', hr', hi', hf'⟩ := h'
  exact ⟨hn'.trans hn, hc'.trans hc, ho'.trans ho, hr'.trans hr,
    fun r hb => (hi' r hb).trans (hi r hb), fun r h0 h1 => (hf' r h0 h1).trans (hf r h0 h1)⟩

theorem initialized_frame (s : State) : Frame s (initialized s) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro r hr
    have h1 : r ≠ 1 := by omega
    have h2 : r ≠ 2 := by omega
    have h3 : r ≠ 3 := by omega
    simp [initialized, writeNat, writeScalar, next, h1, h2, h3]
  · intro r h0 h1
    simp [initialized, writeNat, writeScalar, next, h0]

theorem round_frame (s : State) : Frame s (roundState s) := by
  by_cases hm : s.natReg 0 % 2 = 0
  all_goals refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
  | solve | simp [roundState, halfState, squaredState, accumulatorState, parityState,
       entered, writeNat, writeScalar, next, hm]
  | (intro r hr
     have h0 : r ≠ 0 := by omega
     have h4 : r ≠ 4 := by omega
     simp [roundState, halfState, squaredState, accumulatorState, parityState,
       entered, writeNat, writeScalar, next, hm, h0, h4])
  | (intro r h0 h1
     simp [roundState, halfState, squaredState, accumulatorState, parityState,
       entered, writeNat, writeScalar, next, hm, h0, h1])

/-- The actual fixed loop halts with accumulator times the prepared base to the exponent.
    Its exact instruction count is loopCost, not an assumed arithmetic budget. -/
theorem loop_correct (e : ℕ) (s : State) (hs : LoopInvariant s) (hexp : s.natReg 0 = e)
    (n : ℕ) (x : Fin n → ℂ) : ∃ u : State,
    Executes program n x s (loopCost e) u ∧
      (u.scalarReg 0).value = (s.scalarReg 0).value * (s.scalarReg 1).value ^ e ∧
      (u.scalarReg 0).dependent = false ∧ Frame s u := by
  induction e using Nat.strong_induction_on generalizing s with
  | h e ih =>
    by_cases he : e = 0
    · obtain ⟨hpc, hzero, hone, htwo, hacc, hbase⟩ := hs
      have hz : s.natReg 0 = 0 := hexp.trans he
      refine ⟨{ s with pc := 11 }, ?_, ?_, hacc, ?_⟩
      · rw [he, loopCost_zero]
        refine .next (u := { s with pc := 11 }) ?_ (.halt ?_)
        all_goals simp [step, program, hpc, hzero, hz]
      · simp [he]
      · exact frame_refl s
    · have hpos : 0 < s.natReg 0 := by omega
      have hnext : (roundState s).natReg 0 = e / 2 := by rw [round_exponent, hexp]
      obtain ⟨u, hu, hvalue, hprepared, hframe⟩ :=
        ih (e / 2) (Nat.div_lt_self (by omega) (by decide)) (roundState s) (round_invariant s hs) hnext
      refine ⟨u, ?_, ?_, hprepared, (round_frame s).trans hframe⟩
      · have hr := round_runs s hs hpos n x
        rw [hexp] at hr
        rw [loopCost_step e he]
        simpa only [Nat.add_comm] using hr.executes hu
      · have hi := round_power_invariant s
        rw [round_exponent, hexp] at hi
        exact hvalue.trans hi

/-- Every successful instruction of this fixed program preserves the word bound.
    Field values are ideal scalars; all integer temporaries remain bounded. -/
theorem step_bound (B : ℕ) (hB : 12 ≤ B) (s u : State) (hs : WordBound B s)
    (n : ℕ) (x : Fin n → ℂ) (h : step program n x s = .running u) : WordBound B u := by
  have hp : s.pc < 12 := by
    by_contra hp
    have hn : program[s.pc]? = none := List.getElem?_eq_none (by simp [program]; omega)
    simp [step, hn] at h
  have hpcnext : s.pc + 1 ≤ B := by omega
  have hn (r v : ℕ) (hv : v ≤ B) : WordBound B (writeNat s r v) :=
    writeNat_bound B s r v hs hpcnext hv
  have hc (r : ℕ) (v : Scalar) : WordBound B (writeScalar s r v) :=
    writeScalar_bound B s r v hs hpcnext
  interval_cases hpc : s.pc
  · simp [step, program, hpc] at h
    subst u; exact hn 1 0 (by omega)
  · simp [step, program, hpc] at h
    subst u; exact hn 2 1 (by omega)
  · simp [step, program, hpc] at h
    subst u; exact hn 3 2 (by omega)
  · simp [step, program, hpc] at h
    subst u; exact hc 0 _
  · simp [step, program, hpc] at h
    subst u
    apply changePC_bound B s _ hs
    split <;> omega
  · by_cases hz : s.natReg 3 = 0
    · simp [step, program, hpc, evalNat, hz] at h
    · simp [step, program, hpc, evalNat, hz] at h
      subst u
      exact hn 4 _ ((Nat.mod_le _ _).trans (hs.2.1 0))
  · simp [step, program, hpc] at h
    subst u
    apply changePC_bound B s _ hs
    split <;> omega
  · cases he : evalField .mul (s.scalarReg 0) (s.scalarReg 1) with
    | none => simp [step, program, hpc, he] at h
    | some v =>
      simp [step, program, hpc, he] at h
      subst u; exact hc 0 v
  · cases he : evalField .mul (s.scalarReg 1) (s.scalarReg 1) with
    | none => simp [step, program, hpc, he] at h
    | some v =>
      simp [step, program, hpc, he] at h
      subst u; exact hc 1 v
  · by_cases hz : s.natReg 3 = 0
    · simp [step, program, hpc, evalNat, hz] at h
    · simp [step, program, hpc, evalNat, hz] at h
      subst u
      exact hn 0 _ ((Nat.div_le_self _ _).trans (hs.2.1 0))
  · simp [step, program, hpc] at h
    subst u; exact changePC_bound B s 4 hs (by omega)
  · simp [step, program, hpc] at h

theorem executes_bounded {B n t : ℕ} {x : Fin n → ℂ} {s u : State}
    (h : Executes program n x s t u) (hB : 12 ≤ B) (hs : WordBound B s) :
    BoundedExecution program n x B s t u := by
  induction h with
  | halt hh => exact .halt hs hh
  | next hh ht ih => exact .next hs hh (ih (step_bound B hB _ _ hs n x hh))

/-- Initialization and the actual loop compute the prepared scalar power. -/
theorem power_correct (s : State) (hpc : s.pc = 0)
    (hb : (s.scalarReg 1).dependent = false) (n : ℕ) (x : Fin n → ℂ) : ∃ u : State,
    Executes program n x s (4 + loopCost (s.natReg 0)) u ∧
      (u.scalarReg 0).value = (s.scalarReg 1).value ^ s.natReg 0 ∧
      (u.scalarReg 0).dependent = false ∧ Frame s u := by
  have hi := initialized_invariant s hpc hb
  have he : (initialized s).natReg 0 = s.natReg 0 := by
    simp [initialized, writeNat, writeScalar, next]
  obtain ⟨u, hu, hv, hd, hf⟩ := loop_correct (s.natReg 0) (initialized s) hi he n x
  refine ⟨u, (initializes s hpc n x).executes hu, ?_, hd, (initialized_frame s).trans hf⟩
  simpa [initialized, writeNat, writeScalar, next] using hv

theorem bounded_power_correct (B : ℕ) (hB : 12 ≤ B) (s : State) (hs : WordBound B s)
    (hpc : s.pc = 0) (hb : (s.scalarReg 1).dependent = false) (n : ℕ) (x : Fin n → ℂ) :
    ∃ u : State, BoundedExecution program n x B s (4 + loopCost (s.natReg 0)) u ∧
      (u.scalarReg 0).value = (s.scalarReg 1).value ^ s.natReg 0 ∧
      (u.scalarReg 0).dependent = false ∧ Frame s u := by
  obtain ⟨u, hu, hv, hd, hf⟩ := power_correct s hpc hb n x
  exact ⟨u, executes_bounded hu hB hs, hv, hd, hf⟩

/-- A prepared input-independent base and integer exponent, with empty heaps. -/
def inputState (b : ℂ) (e : ℕ) : State :=
  ⟨0, Function.update (fun _ => 0) 0 e,
    Function.update (fun _ => Scalar.zero) 1 ⟨b, false⟩,
    fun _ => none, fun _ => none, fun _ => none, []⟩

theorem inputState_bound (b : ℂ) (e : ℕ) : WordBound (e + 12) (inputState b e) := by
  refine ⟨by simp [inputState], ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    by_cases hr : r = 0 <;> simp [inputState, hr]
  · simp [inputState]
  · simp [inputState]
  · simp [inputState]
  · simp [inputState]

/-- One fixed program, arbitrary prepared complex base and exponent, logarithmic
    instruction count, and a linear integer bound on every intermediate state. -/
theorem canonical_power (b : ℂ) (e n : ℕ) (x : Fin n → ℂ) : ∃ u : State,
    BoundedExecution program n x (e + 12) (inputState b e) (4 + loopCost e) u ∧
      (u.scalarReg 0).value = b ^ e ∧ (u.scalarReg 0).dependent = false ∧
      Frame (inputState b e) u := by
  simpa [inputState] using
    bounded_power_correct (e + 12) (by omega) (inputState b e) (inputState_bound b e)
      (by rfl) (by simp [inputState]) n x

theorem canonical_power_log (b : ℂ) (e n : ℕ) (x : Fin n → ℂ) :
    ∃ t : ℕ, ∃ u : State,
      BoundedExecution program n x (e + 12) (inputState b e) t u ∧
      (u.scalarReg 0).value = b ^ e ∧ (u.scalarReg 0).dependent = false ∧
      Frame (inputState b e) u ∧ t ≤ 7 * (Nat.log2 (e + 1) + 1) + 6 := by
  obtain ⟨u, hu, hv, hd, hf⟩ := canonical_power b e n x
  exact ⟨4 + loopCost e, u, hu, hv, hd, hf, totalCost_log_bound e⟩

/-- Any execution from a prepared base has the proved exact instruction count. -/
theorem power_count_exact (s : State) (hpc : s.pc = 0)
    (hb : (s.scalarReg 1).dependent = false) (n : ℕ) (x : Fin n → ℂ)
    (t : ℕ) (u : State) (h : Executes program n x s t u) :
    t = 4 + loopCost (s.natReg 0) := by
  obtain ⟨v, hv, _⟩ := power_correct s hpc hb n x
  exact (h.deterministic hv).1

/-- With the two scalar workspace registers prepared, every input-dependent
    scalar register is preserved, as are both heaps, outputs, and root requests. -/
theorem dependent_register_preserved {s u : State} (hf : Frame s u)
    (ha : (s.scalarReg 0).dependent = false) (hb : (s.scalarReg 1).dependent = false)
    (r : ℕ) (hr : (s.scalarReg r).dependent = true) : u.scalarReg r = s.scalarReg r := by
  have h0 : r ≠ 0 := by intro h; subst r; rw [ha] at hr; contradiction
  have h1 : r ≠ 1 := by intro h; subst r; rw [hb] at hr; contradiction
  exact hf.2.2.2.2.2 r h0 h1

/-- Actual charged extraction from an already prepared specified root. The
    program makes no further root request and does not inspect complex values. -/
theorem specified_root_extract (D d : ℕ) (hD : 0 < D) (hd : 0 < d) (hdiv : d ∣ D)
    (n : ℕ) (x : Fin n → ℂ) : ∃ u : State,
    BoundedExecution program n x (D / d + 12)
      (inputState (OAI.ExactFourier.zeta D) (D / d)) (4 + loopCost (D / d)) u ∧
      (u.scalarReg 0).value = OAI.ExactFourier.zeta d ∧
      (u.scalarReg 0).dependent = false ∧
      Frame (inputState (OAI.ExactFourier.zeta D) (D / d)) u := by
  obtain ⟨u, hu, hv, hdep, hf⟩ := canonical_power (OAI.ExactFourier.zeta D) (D / d) n x
  exact ⟨u, hu, hv.trans (UniformRoots.specifiedRoot_divisor_power D d hD hd hdiv), hdep, hf⟩

end
end ExactFourierCircuits.UniformPowerMachine

import UniformPowerMachine

set_option autoImplicit false

namespace ExactFourierCircuits.UniformIntegerScalarMachine
open UniformMachine
noncomputable section

/- Nat workspace: remaining integer=0, zero=1, one=2, two=3, parity=4.
   Scalar workspace: accumulated integer=0, place value=1. -/
def block (b : ℕ) : Program :=
  [.natLiteral 1 0, .natLiteral 2 1, .natLiteral 3 2, .scalarLiteral 0 0,
   .scalarLiteral 1 1, .branchLT 1 0 (b + 6) (b + 12), .natBinary .mod 4 0 3,
   .branchLT 1 4 (b + 8) (b + 9), .fieldBinary .add 0 0 1,
   .fieldBinary .add 1 1 1, .natBinary .div 0 0 3, .jump (b + 5)]

def naturalProgram : Program := block 0 ++ [.halt]
def rationalProgram : Program := block 0 ++
  [.scalarLiteral 3 0, .fieldBinary .add 2 0 3, .natBinary .sub 0 5 1] ++
  block 15 ++ [.fieldBinary .div 2 2 0, .halt]

/-- Nat register 6 is a sign flag: zero is positive, nonzero is negative. -/
def signedProgram : Program := rationalProgram.take 28 ++
  [.branchLT 1 6 29 30, .fieldBinary .sub 2 3 2, .halt]

/-- A syntactic literal instruction block, not an assumed state transformer. -/
def CodeAt (p : Program) (b : ℕ) : Prop :=
  ∀ i : ℕ, i < 12 → p[b + i]? = (block b)[i]?

theorem natural_code : CodeAt naturalProgram 0 := by
  intro i hi
  interval_cases i <;> rfl

theorem rational_first_code : CodeAt rationalProgram 0 := by
  intro i hi
  interval_cases i <;> rfl

theorem rational_second_code : CodeAt rationalProgram 15 := by
  intro i hi
  interval_cases i <;> rfl

def initialized (s : State) : State :=
  writeScalar (writeScalar (writeNat (writeNat (writeNat s 1 0) 2 1) 3 2) 0 ⟨0, false⟩)
    1 ⟨1, false⟩

def Invariant (b : ℕ) (s : State) : Prop :=
  s.pc = b + 5 ∧ s.natReg 1 = 0 ∧ s.natReg 2 = 1 ∧ s.natReg 3 = 2 ∧
    (s.scalarReg 0).dependent = false ∧ (s.scalarReg 1).dependent = false

def entered (b : ℕ) (s : State) : State := { s with pc := b + 6 }
def parityState (b : ℕ) (s : State) : State := writeNat (entered b s) 4 (s.natReg 0 % 2)
def accumulatorState (b : ℕ) (s : State) : State :=
  if s.natReg 0 % 2 = 0 then { parityState b s with pc := b + 9 }
  else writeScalar { parityState b s with pc := b + 8 } 0
    ⟨(s.scalarReg 0).value + (s.scalarReg 1).value, false⟩
def doubledState (b : ℕ) (s : State) : State := writeScalar (accumulatorState b s) 1
  ⟨(s.scalarReg 1).value + (s.scalarReg 1).value, false⟩
def halfState (b : ℕ) (s : State) : State := writeNat (doubledState b s) 0 (s.natReg 0 / 2)
def roundState (b : ℕ) (s : State) : State := { halfState b s with pc := b + 5 }

def loopSteps (e : ℕ) : ℕ :=
  if _h : e = 0 then 1 else loopSteps (e / 2) + UniformPowerMachine.roundCost e
termination_by e
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

theorem loopSteps_zero : loopSteps 0 = 1 := by rw [loopSteps]; rfl
theorem loopSteps_step (e : ℕ) (he : e ≠ 0) :
    loopSteps e = loopSteps (e / 2) + UniformPowerMachine.roundCost e := by
  rw [loopSteps, dite_eq_right he]

theorem loopSteps_powerCost (e : ℕ) : loopSteps e + 1 = UniformPowerMachine.loopCost e := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases he : e = 0
    · subst e; rw [loopSteps_zero, UniformPowerMachine.loopCost_zero]
    · rw [loopSteps_step e he, UniformPowerMachine.loopCost_step e he]
      have hi := ih (e / 2) (Nat.div_lt_self (by omega) (by decide))
      omega

theorem initializes (p : Program) (b : ℕ) (hc : CodeAt p b) (s : State) (hp : s.pc = b)
    (n : ℕ) (x : Fin n → ℂ) : Runs p n x s 5 (initialized s) := by
  have h0 : p[b]? = some (.natLiteral 1 0) := by simpa [block] using hc 0 (by decide)
  have h1 := hc 1 (by decide)
  have h2 := hc 2 (by decide)
  have h3 := hc 3 (by decide)
  have h4 := hc 4 (by decide)
  refine .next (u := writeNat s 1 0) ?_ (.next (u := writeNat (writeNat s 1 0) 2 1) ?_
    (.next (u := writeNat (writeNat (writeNat s 1 0) 2 1) 3 2) ?_
      (.next (u := writeScalar (writeNat (writeNat (writeNat s 1 0) 2 1) 3 2) 0 ⟨0, false⟩) ?_
        (.next (u := initialized s) ?_ (.refl _)))))
  all_goals simp [step, initialized, writeNat, writeScalar, next, hp,
    Nat.add_assoc, h0, h1, h2, h3, h4, block]

theorem initialized_invariant (b : ℕ) (s : State) (hp : s.pc = b) :
    Invariant b (initialized s) := by
  simp [Invariant, initialized, writeNat, writeScalar, next, hp, Nat.add_assoc]

theorem round_invariant (b : ℕ) (s : State) (hs : Invariant b s) :
    Invariant b (roundState b s) := by
  obtain ⟨hp, hz, hone, htwo, ha, hd⟩ := hs
  by_cases hm : s.natReg 0 % 2 = 0 <;>
    simp [Invariant, roundState, halfState, doubledState, accumulatorState,
      parityState, entered, writeNat, writeScalar, next, hm, hz, hone, htwo, ha]

theorem round_remaining (b : ℕ) (s : State) : (roundState b s).natReg 0 = s.natReg 0 / 2 := by
  simp [roundState, halfState, writeNat]

theorem round_values (b : ℕ) (s : State) :
    (roundState b s).scalarReg 0 =
      (if s.natReg 0 % 2 = 0 then s.scalarReg 0 else
        ⟨(s.scalarReg 0).value + (s.scalarReg 1).value, false⟩) ∧
    (roundState b s).scalarReg 1 =
      ⟨(s.scalarReg 1).value + (s.scalarReg 1).value, false⟩ := by
  by_cases hm : s.natReg 0 % 2 = 0 <;>
    simp [roundState, halfState, doubledState, accumulatorState, parityState,
      entered, writeNat, writeScalar, next, hm]

theorem round_cast_invariant (b : ℕ) (s : State) :
    ((roundState b s).scalarReg 0).value +
      ((roundState b s).scalarReg 1).value * ((roundState b s).natReg 0 : ℂ) =
    (s.scalarReg 0).value + (s.scalarReg 1).value * (s.natReg 0 : ℂ) := by
  obtain ⟨ha, hd⟩ := round_values b s
  rw [round_remaining, ha, hd]
  have hm := Nat.mod_lt (s.natReg 0) (by decide : 0 < 2)
  have heq := Nat.div_add_mod (s.natReg 0) 2
  by_cases he : s.natReg 0 % 2 = 0
  · rw [ite_eq_left he]
    have hx : s.natReg 0 = 2 * (s.natReg 0 / 2) := by omega
    conv_rhs => rw [hx]
    push_cast
    ring
  · rw [ite_eq_right he]
    have hx : s.natReg 0 = 2 * (s.natReg 0 / 2) + 1 := by omega
    conv_rhs => rw [hx]
    push_cast
    ring

theorem round_runs (p : Program) (b : ℕ) (hc : CodeAt p b) (s : State)
    (hs : Invariant b s) (he : 0 < s.natReg 0) (n : ℕ) (x : Fin n → ℂ) :
    Runs p n x s (UniformPowerMachine.roundCost (s.natReg 0)) (roundState b s) := by
  obtain ⟨hp, hz, hone, htwo, ha, hd⟩ := hs
  have h5 := hc 5 (by decide)
  have h6 := hc 6 (by decide)
  have h7 := hc 7 (by decide)
  have h8 := hc 8 (by decide)
  have h9 := hc 9 (by decide)
  have h10 := hc 10 (by decide)
  have h11 := hc 11 (by decide)
  by_cases hm : s.natReg 0 % 2 = 0
  · rw [UniformPowerMachine.roundCost, ite_eq_left hm]
    refine .next (u := entered b s) ?_ (.next (u := parityState b s) ?_
      (.next (u := { parityState b s with pc := b + 9 }) ?_
        (.next (u := doubledState b s) ?_ (.next (u := halfState b s) ?_
          (.next (u := roundState b s) ?_ (.refl _))))))
    all_goals simp [step, evalNat, evalField, roundState, halfState, doubledState,
      accumulatorState, parityState, entered, writeNat, writeScalar, next,
      hp, hz, htwo, hd, hm, he, Nat.add_assoc, h5, h6, h7, h9, h10, h11, block]
  · have hmpos : 0 < s.natReg 0 % 2 := Nat.pos_of_ne_zero hm
    rw [UniformPowerMachine.roundCost, ite_eq_right hm]
    refine .next (u := entered b s) ?_ (.next (u := parityState b s) ?_
      (.next (u := { parityState b s with pc := b + 8 }) ?_
        (.next (u := accumulatorState b s) ?_ (.next (u := doubledState b s) ?_
          (.next (u := halfState b s) ?_ (.next (u := roundState b s) ?_ (.refl _)))))))
    all_goals simp [step, evalNat, evalField, roundState, halfState, doubledState,
      accumulatorState, parityState, entered, writeNat, writeScalar, next,
      hp, hz, htwo, ha, hd, hm, he, hmpos, Nat.add_assoc, h5, h6, h7, h8, h9, h10, h11, block]

theorem initialized_frame (s : State) : UniformPowerMachine.Frame s (initialized s) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro r hr
    have h1 : r ≠ 1 := by omega
    have h2 : r ≠ 2 := by omega
    have h3 : r ≠ 3 := by omega
    simp [initialized, writeNat, writeScalar, next, h1, h2, h3]
  · intro r h0 h1
    simp [initialized, writeNat, writeScalar, next, h0, h1]

theorem round_frame (b : ℕ) (s : State) : UniformPowerMachine.Frame s (roundState b s) := by
  by_cases hm : s.natReg 0 % 2 = 0
  all_goals refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
  | solve | simp [roundState, halfState, doubledState, accumulatorState, parityState,
      entered, writeNat, writeScalar, next, hm]
  | (intro r hr
     have h0 : r ≠ 0 := by omega
     have h4 : r ≠ 4 := by omega
     simp [roundState, halfState, doubledState, accumulatorState, parityState,
       entered, writeNat, writeScalar, next, hm, h0, h4])
  | (intro r h0 h1
     simp [roundState, halfState, doubledState, accumulatorState, parityState,
       entered, writeNat, writeScalar, next, hm, h0, h1])

theorem loop_correct (p : Program) (b : ℕ) (hc : CodeAt p b) (e : ℕ) (s : State)
    (hs : Invariant b s) (he : s.natReg 0 = e) (n : ℕ) (x : Fin n → ℂ) : ∃ u : State,
    Runs p n x s (loopSteps e) u ∧ u.pc = b + 12 ∧ u.natReg 0 = 0 ∧
      (u.scalarReg 0).value = (s.scalarReg 0).value + (s.scalarReg 1).value * (e : ℂ) ∧
      (u.scalarReg 0).dependent = false ∧ u.natReg 1 = 0 ∧ UniformPowerMachine.Frame s u := by
  induction e using Nat.strong_induction_on generalizing s with
  | h e ih =>
    by_cases hz : e = 0
    · have hrem : s.natReg 0 = 0 := he.trans hz
      obtain ⟨hp, hzero, _, _, hacc, _⟩ := hs
      refine ⟨{ s with pc := b + 12 }, ?_, rfl, hrem, ?_, hacc, hzero,
        UniformPowerMachine.frame_refl s⟩
      · rw [hz, loopSteps_zero]
        refine .next ?_ (.refl _)
        simp [step, hp, hc 5 (by decide), block, hzero, hrem]
      · simp [hz]
    · have hpos : 0 < s.natReg 0 := by omega
      have hnext : (roundState b s).natReg 0 = e / 2 := by rw [round_remaining, he]
      obtain ⟨u, hu, hp, hr, hv, hd, hzero, hf⟩ :=
        ih (e / 2) (Nat.div_lt_self (by omega) (by decide)) (roundState b s)
          (round_invariant b s hs) hnext
      refine ⟨u, ?_, hp, hr, ?_, hd, hzero, (round_frame b s).trans hf⟩
      · have hrun := round_runs p b hc s hs hpos n x
        rw [he] at hrun
        rw [loopSteps_step e hz]
        simpa only [Nat.add_comm] using hrun.trans hu
      · have hi := round_cast_invariant b s
        rw [round_remaining, he] at hi
        exact hv.trans hi

theorem block_correct (p : Program) (b : ℕ) (hc : CodeAt p b) (s : State) (hp : s.pc = b)
    (n : ℕ) (x : Fin n → ℂ) : ∃ u : State,
    Runs p n x s (4 + UniformPowerMachine.loopCost (s.natReg 0)) u ∧ u.pc = b + 12 ∧
      u.natReg 0 = 0 ∧ (u.scalarReg 0).value = (s.natReg 0 : ℂ) ∧
      (u.scalarReg 0).dependent = false ∧ u.natReg 1 = 0 ∧ UniformPowerMachine.Frame s u := by
  have he : (initialized s).natReg 0 = s.natReg 0 := by
    simp [initialized, writeNat, writeScalar, next]
  obtain ⟨u, hu, huPC, huRem, hv, hd, hz, hf⟩ :=
    loop_correct p b hc (s.natReg 0) (initialized s) (initialized_invariant b s hp) he n x
  refine ⟨u, ?_, huPC, huRem, ?_, hd, hz, (initialized_frame s).trans hf⟩
  · have hrun := (initializes p b hc s hp n x).trans hu
    convert hrun using 1
    have hsteps := loopSteps_powerCost (s.natReg 0)
    omega
  · simpa [initialized, writeNat, writeScalar, next] using hv

theorem natural_correct (s : State) (hp : s.pc = 0) (n : ℕ) (x : Fin n → ℂ) : ∃ u : State,
    Executes naturalProgram n x s (5 + UniformPowerMachine.loopCost (s.natReg 0)) u ∧
      (u.scalarReg 0).value = (s.natReg 0 : ℂ) ∧ (u.scalarReg 0).dependent = false ∧
      UniformPowerMachine.Frame s u := by
  obtain ⟨u, hu, huPC, _, hv, hd, _, hf⟩ := block_correct naturalProgram 0 natural_code s hp n x
  have hh : Executes naturalProgram n x u 1 u := .halt (by simp [step, huPC, naturalProgram, block])
  refine ⟨u, ?_, hv, hd, hf⟩
  convert hu.executes hh using 1
  omega

theorem natural_cost_bound (e : ℕ) :
    5 + UniformPowerMachine.loopCost e ≤ 7 * (Nat.log2 (e + 1) + 1) + 7 := by
  have h := UniformPowerMachine.totalCost_log_bound e
  omega

/-- These instructions cannot increase an integer beyond a source register or
    a fixed literal; field instructions change no integer or heap. -/
def SafeInstruction (B : ℕ) : Instruction → Prop
  | .natLiteral _ v => v ≤ B
  | .natBinary op _ _ _ => op ≠ .add ∧ op ≠ .mul
  | .scalarLiteral _ _ => True
  | .fieldBinary _ _ _ _ => True
  | .branchLT _ _ yes no => yes ≤ B ∧ no ≤ B
  | .jump target => target ≤ B
  | .halt => True
  | _ => False

def SafeProgram (B : ℕ) (p : Program) : Prop := ∀ i ∈ p, SafeInstruction B i

theorem safe_step_bound (p : Program) (B : ℕ) (hl : p.length ≤ B) (hp : SafeProgram B p)
    (s u : State) (hs : WordBound B s) (n : ℕ) (x : Fin n → ℂ)
    (h : step p n x s = .running u) : WordBound B u := by
  cases hg : p[s.pc]? with
  | none => simp [step, hg] at h
  | some ins =>
    have hi := hp ins (List.mem_of_getElem? hg)
    have hpc : s.pc + 1 ≤ B := by
      have hlen := (List.getElem?_eq_some_iff.1 hg).choose
      omega
    have hnat (r v : ℕ) (hv : v ≤ B) : WordBound B (writeNat s r v) :=
      writeNat_bound B s r v hs hpc hv
    have hscalar (r : ℕ) (v : Scalar) : WordBound B (writeScalar s r v) :=
      writeScalar_bound B s r v hs hpc
    cases ins with
    | natLiteral r v =>
      simp [step, hg] at h
      subst u; exact hnat r v hi
    | natBinary op dst left right =>
      cases op with
      | add => simp [SafeInstruction] at hi
      | mul => simp [SafeInstruction] at hi
      | sub =>
        simp [step, hg, evalNat] at h
        subst u; exact hnat dst _ ((Nat.sub_le _ _).trans (hs.2.1 left))
      | div =>
        by_cases hz : s.natReg right = 0
        · simp [step, hg, evalNat, hz] at h
        · simp [step, hg, evalNat, hz] at h
          subst u; exact hnat dst _ ((Nat.div_le_self _ _).trans (hs.2.1 left))
      | mod =>
        by_cases hz : s.natReg right = 0
        · simp [step, hg, evalNat, hz] at h
        · simp [step, hg, evalNat, hz] at h
          subst u; exact hnat dst _ ((Nat.mod_le _ _).trans (hs.2.1 left))
    | scalarLiteral r v =>
      simp [step, hg] at h
      subst u; exact hscalar r _
    | fieldBinary op dst left right =>
      obtain ⟨v, rfl⟩ := field_step_write hg h
      exact hscalar dst v
    | branchLT left right yes no =>
      simp [step, hg] at h
      subst u
      apply changePC_bound B s _ hs
      change yes ≤ B ∧ no ≤ B at hi
      split
      · exact hi.1
      · exact hi.2
    | jump target =>
      simp [step, hg] at h
      subst u; exact changePC_bound B s target hs hi
    | halt => simp [step, hg] at h
    | length _ => simp [SafeInstruction] at hi
    | input _ _ => simp [SafeInstruction] at hi
    | root _ _ => simp [SafeInstruction] at hi
    | loadNat _ _ => simp [SafeInstruction] at hi
    | storeNat _ _ => simp [SafeInstruction] at hi
    | loadScalar _ _ => simp [SafeInstruction] at hi
    | storeScalar _ _ => simp [SafeInstruction] at hi
    | output _ _ => simp [SafeInstruction] at hi

theorem natural_safe (B : ℕ) (hB : 13 ≤ B) : SafeProgram B naturalProgram := by
  simp [SafeProgram, naturalProgram, block, SafeInstruction]; omega

theorem rational_safe (B : ℕ) (hB : 29 ≤ B) : SafeProgram B rationalProgram := by
  simp [SafeProgram, rationalProgram, block, SafeInstruction]; omega

theorem bounded_natural_correct (B : ℕ) (hB : 13 ≤ B) (s : State) (hs : WordBound B s)
    (hpc : s.pc = 0) (n : ℕ) (x : Fin n → ℂ) : ∃ u : State,
    BoundedExecution naturalProgram n x B s (5 + UniformPowerMachine.loopCost (s.natReg 0)) u ∧
      (u.scalarReg 0).value = (s.natReg 0 : ℂ) ∧ (u.scalarReg 0).dependent = false ∧
      UniformPowerMachine.Frame s u := by
  obtain ⟨u, hu, hv, hd, hf⟩ := natural_correct s hpc n x
  refine ⟨u, ?_, hv, hd, hf⟩
  exact hu.bounded_of_invariant (WordBound B) hs (fun _ h => h)
    (fun s u h => safe_step_bound naturalProgram B (by simpa [naturalProgram, block] using hB)
      (natural_safe B hB) s u h n x)

def bridgeZero (s : State) : State := writeScalar s 3 ⟨0, false⟩
def bridgeNumerator (s : State) : State := writeScalar (bridgeZero s) 2
  ⟨(s.scalarReg 0).value, false⟩
def bridgeState (s : State) : State := writeNat (bridgeNumerator s) 0 (s.natReg 5)

theorem bridge_runs (s : State) (hpc : s.pc = 12) (hz : s.natReg 1 = 0)
    (ha : (s.scalarReg 0).dependent = false) (n : ℕ) (x : Fin n → ℂ) :
    Runs rationalProgram n x s 3 (bridgeState s) := by
  refine .next (u := bridgeZero s) ?_ (.next (u := bridgeNumerator s) ?_
    (.next (u := bridgeState s) ?_ (.refl _)))
  all_goals simp [step, rationalProgram, block, bridgeZero, bridgeNumerator, bridgeState,
    writeNat, writeScalar, next, hpc, hz, ha, evalField, evalNat]

def RationalFrame (s u : State) : Prop :=
  u.natHeap = s.natHeap ∧ u.scalarHeap = s.scalarHeap ∧ u.outputs = s.outputs ∧
    u.rootOrders = s.rootOrders ∧ (∀ r, 5 ≤ r → u.natReg r = s.natReg r) ∧
      (∀ r, 4 ≤ r → u.scalarReg r = s.scalarReg r)

theorem RationalFrame.trans {s u v : State} (h : RationalFrame s u)
    (h' : RationalFrame u v) : RationalFrame s v := by
  obtain ⟨hn, hc, ho, hr, hi, hf⟩ := h
  obtain ⟨hn', hc', ho', hr', hi', hf'⟩ := h'
  exact ⟨hn'.trans hn, hc'.trans hc, ho'.trans ho, hr'.trans hr,
    fun r hb => (hi' r hb).trans (hi r hb), fun r hb => (hf' r hb).trans (hf r hb)⟩

theorem frame_weaken {s u : State} (h : UniformPowerMachine.Frame s u) : RationalFrame s u := by
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    fun r hr => h.2.2.2.2.2 r (by omega) (by omega)⟩

theorem bridge_frame (s : State) : RationalFrame s (bridgeState s) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro r hr
    have h0 : r ≠ 0 := by omega
    simp [bridgeState, bridgeNumerator, bridgeZero, writeNat, writeScalar, next, h0]
  · intro r hr
    have h2 : r ≠ 2 := by omega
    have h3 : r ≠ 3 := by omega
    simp [bridgeState, bridgeNumerator, bridgeZero, writeNat, writeScalar, next, h2, h3]

theorem rational_correct_workspace (s : State) (hpc : s.pc = 0) (hden : 0 < s.natReg 5)
    (n : ℕ) (x : Fin n → ℂ) : ∃ u : State,
    Executes rationalProgram n x s
      (13 + UniformPowerMachine.loopCost (s.natReg 0) + UniformPowerMachine.loopCost (s.natReg 5)) u ∧
      (u.scalarReg 2).value = (s.natReg 0 : ℂ) / (s.natReg 5 : ℂ) ∧
      (u.scalarReg 2).dependent = false ∧ u.pc = 28 ∧ u.natReg 1 = 0 ∧
      u.scalarReg 3 = ⟨0, false⟩ ∧ RationalFrame s u := by
  obtain ⟨v, hv, hvPC, _, hvval, hvdep, hvzero, hvframe⟩ :=
    block_correct rationalProgram 0 rational_first_code s hpc n x
  have hvden : v.natReg 5 = s.natReg 5 := hvframe.2.2.2.2.1 5 (by decide)
  have hbPC : (bridgeState v).pc = 15 := by
    simp [bridgeState, bridgeNumerator, bridgeZero, writeNat, writeScalar, next, hvPC]
  have hbden : (bridgeState v).natReg 0 = s.natReg 5 := by
    simp [bridgeState, writeNat, hvden]
  obtain ⟨w, hw, hwPC, _, hwval, hwdep, hwzero, hwframe⟩ :=
    block_correct rationalProgram 15 rational_second_code (bridgeState v) hbPC n x
  have hnum : w.scalarReg 2 = ⟨(s.natReg 0 : ℂ), false⟩ := by
    rw [hwframe.2.2.2.2.2 2 (by decide) (by decide)]
    simp [bridgeState, bridgeNumerator, bridgeZero, writeNat, writeScalar, next, hvval]
  have hdivisor : (w.scalarReg 0).value = (s.natReg 5 : ℂ) := by simpa [hbden] using hwval
  have hscalarZero : w.scalarReg 3 = ⟨0, false⟩ := by
    rw [hwframe.2.2.2.2.2 3 (by decide) (by decide)]
    simp [bridgeState, bridgeNumerator, bridgeZero, writeNat, writeScalar, next]
  let u := writeScalar w 2 ⟨(s.natReg 0 : ℂ) / (s.natReg 5 : ℂ), false⟩
  have hfinish : Executes rationalProgram n x w 2 u := by
    refine .next (u := u) ?_ (.halt ?_)
    · simp [step, rationalProgram, block, hwPC, evalField, hwdep, hnum,
        hdivisor, hden.ne', u]
    · simp [step, rationalProgram, block, u, writeScalar, next, hwPC]
  refine ⟨u, ?_, ?_, ?_, ?_, hwzero, ?_, ?_⟩
  · have hbridge := bridge_runs v hvPC hvzero hvdep n x
    have hall := ((hv.trans hbridge).trans hw).executes hfinish
    rw [hbden] at hall
    convert hall using 1
    omega
  · simp [u, writeScalar]
  · simp [u, writeScalar]
  · simp [u, writeScalar, next, hwPC]
  · simpa [u, writeScalar, next] using hscalarZero
  · have hbefore := ((frame_weaken hvframe).trans (bridge_frame v)).trans (frame_weaken hwframe)
    have hlast : RationalFrame w u := by
      refine ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
      intro r hr
      have h2 : r ≠ 2 := by omega
      simp [u, writeScalar, next, h2]
    exact hbefore.trans hlast

theorem rational_correct (s : State) (hpc : s.pc = 0) (hden : 0 < s.natReg 5)
    (n : ℕ) (x : Fin n → ℂ) : ∃ u : State,
    Executes rationalProgram n x s
      (13 + UniformPowerMachine.loopCost (s.natReg 0) + UniformPowerMachine.loopCost (s.natReg 5)) u ∧
      (u.scalarReg 2).value = (s.natReg 0 : ℂ) / (s.natReg 5 : ℂ) ∧
      (u.scalarReg 2).dependent = false ∧ RationalFrame s u := by
  obtain ⟨u, hu, hv, hd, _, _, _, hf⟩ := rational_correct_workspace s hpc hden n x
  exact ⟨u, hu, hv, hd, hf⟩

theorem rational_cost_bound (a d : ℕ) :
    13 + UniformPowerMachine.loopCost a + UniformPowerMachine.loopCost d ≤
      7 * ((Nat.log2 (a + 1) + 1) + (Nat.log2 (d + 1) + 1)) + 17 := by
  have ha := UniformPowerMachine.totalCost_log_bound a
  have hd := UniformPowerMachine.totalCost_log_bound d
  omega

theorem bounded_rational_correct (B : ℕ) (hB : 29 ≤ B) (s : State) (hs : WordBound B s)
    (hpc : s.pc = 0) (hden : 0 < s.natReg 5) (n : ℕ) (x : Fin n → ℂ) : ∃ u : State,
    BoundedExecution rationalProgram n x B s
      (13 + UniformPowerMachine.loopCost (s.natReg 0) + UniformPowerMachine.loopCost (s.natReg 5)) u ∧
      (u.scalarReg 2).value = (s.natReg 0 : ℂ) / (s.natReg 5 : ℂ) ∧
      (u.scalarReg 2).dependent = false ∧ RationalFrame s u := by
  obtain ⟨u, hu, hv, hd, hf⟩ := rational_correct s hpc hden n x
  refine ⟨u, ?_, hv, hd, hf⟩
  exact hu.bounded_of_invariant (WordBound B) hs (fun _ h => h)
    (fun s u h => safe_step_bound rationalProgram B (by simpa [rationalProgram, block] using hB)
      (rational_safe B hB) s u h n x)

theorem signed_prefix (i : ℕ) (hi : i < 28) : signedProgram[i]? = rationalProgram[i]? := by
  interval_cases i <;> rfl

theorem rational_running_pc (s u : State) (n : ℕ) (x : Fin n → ℂ)
    (h : step rationalProgram n x s = .running u) : s.pc < 28 := by
  by_contra hp
  by_cases he : s.pc = 28
  · simp [step, rationalProgram, block, he] at h
  · have hn : rationalProgram[s.pc]? = none := List.getElem?_eq_none
      (by simp [rationalProgram, block]; omega)
    simp [step, hn] at h

/-- Reuse the actual unsigned execution before its halt; the signed program
    literally has the same first 28 instructions. -/
theorem rational_to_signed {n t : ℕ} {x : Fin n → ℂ} {s u : State}
    (h : Executes rationalProgram n x s t u) :
    ∃ k : ℕ, t = k + 1 ∧ Runs signedProgram n x s k u := by
  induction h with
  | halt _ => exact ⟨0, rfl, .refl _⟩
  | @next s' u' _ _ hh _ ih =>
    obtain ⟨k, hk, hr⟩ := ih
    have he : step signedProgram n x s' = .running u' := by
      simp only [step, signed_prefix _ (rational_running_pc s' u' n x hh)]
      exact hh
    exact ⟨k + 1, by omega, .next he hr⟩

def signCost (flag : ℕ) : ℕ := if flag = 0 then 1 else 2
def signedValue (a d flag : ℕ) : ℂ :=
  if flag = 0 then (a : ℂ) / (d : ℂ) else -((a : ℂ) / (d : ℂ))

theorem signed_correct (s : State) (hpc : s.pc = 0) (hden : 0 < s.natReg 5)
    (n : ℕ) (x : Fin n → ℂ) : ∃ u : State,
    Executes signedProgram n x s
      (13 + UniformPowerMachine.loopCost (s.natReg 0) + UniformPowerMachine.loopCost (s.natReg 5)
        + signCost (s.natReg 6)) u ∧
      (u.scalarReg 2).value = signedValue (s.natReg 0) (s.natReg 5) (s.natReg 6) ∧
      (u.scalarReg 2).dependent = false ∧ RationalFrame s u := by
  obtain ⟨v, hv, hval, hdep, hp, hz, hscalarZero, hf⟩ := rational_correct_workspace s hpc hden n x
  obtain ⟨k, hk, hr⟩ := rational_to_signed hv
  have hflag : v.natReg 6 = s.natReg 6 := hf.2.2.2.2.1 6 (by decide)
  by_cases hsign : s.natReg 6 = 0
  · let u : State := { v with pc := 30 }
    have htail : Executes signedProgram n x v 2 u := by
      refine .next (u := u) ?_ (.halt ?_)
      · simp [step, signedProgram, rationalProgram, block, hp, hz, hflag, hsign, u]
      · simp [step, signedProgram, rationalProgram, block, u]
    refine ⟨u, ?_, ?_, hdep, hf⟩
    · have hh := hr.executes htail
      convert hh using 1
      simp only [signCost, hsign, ite_true]
      omega
    · simpa [u, signedValue, hsign] using hval
  · have hpositive : 0 < s.natReg 6 := Nat.pos_of_ne_zero hsign
    let entered : State := { v with pc := 29 }
    let u : State := writeScalar entered 2
      ⟨-((s.natReg 0 : ℂ) / (s.natReg 5 : ℂ)), false⟩
    have htail : Executes signedProgram n x v 3 u := by
      refine .next (u := entered) ?_ (.next (u := u) ?_ (.halt ?_))
      · simp [step, signedProgram, rationalProgram, block, hp, hz, hflag, hpositive, entered]
      · simp [step, signedProgram, rationalProgram, block, entered, evalField, hscalarZero,
          hval, hdep, u]
      · simp [step, signedProgram, rationalProgram, block, u, entered, writeScalar, next]
    refine ⟨u, ?_, ?_, ?_, ?_⟩
    · have hh := hr.executes htail
      convert hh using 1
      simp only [signCost, ite_eq_right hsign]
      omega
    · simp [u, writeScalar, signedValue, hsign]
    · simp [u, writeScalar]
    · apply hf.trans
      refine ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
      intro r hbound
      have h2 : r ≠ 2 := by omega
      simp [u, entered, writeScalar, next, h2]

theorem signed_safe (B : ℕ) (hB : 31 ≤ B) : SafeProgram B signedProgram := by
  simp [SafeProgram, signedProgram, rationalProgram, block, SafeInstruction]; omega

theorem signed_cost_bound (a d flag : ℕ) :
    13 + UniformPowerMachine.loopCost a + UniformPowerMachine.loopCost d + signCost flag ≤
      7 * ((Nat.log2 (a + 1) + 1) + (Nat.log2 (d + 1) + 1)) + 19 := by
  have hc := rational_cost_bound a d
  have hsign : signCost flag ≤ 2 := by unfold signCost; split <;> omega
  omega

theorem bounded_signed_correct (B : ℕ) (hB : 31 ≤ B) (s : State) (hs : WordBound B s)
    (hpc : s.pc = 0) (hden : 0 < s.natReg 5) (n : ℕ) (x : Fin n → ℂ) : ∃ u : State,
    BoundedExecution signedProgram n x B s
      (13 + UniformPowerMachine.loopCost (s.natReg 0) + UniformPowerMachine.loopCost (s.natReg 5)
        + signCost (s.natReg 6)) u ∧
      (u.scalarReg 2).value = signedValue (s.natReg 0) (s.natReg 5) (s.natReg 6) ∧
      (u.scalarReg 2).dependent = false ∧ RationalFrame s u := by
  obtain ⟨u, hu, hv, hd, hf⟩ := signed_correct s hpc hden n x
  refine ⟨u, ?_, hv, hd, hf⟩
  exact hu.bounded_of_invariant (WordBound B) hs (fun _ h => h)
    (fun s u h => safe_step_bound signedProgram B (by simpa [signedProgram, rationalProgram, block] using hB)
      (signed_safe B hB) s u h n x)

/-- Prepared integer arguments and sign; no input array or root is accessed. -/
def inputState (a d flag : ℕ) : State :=
  ⟨0, fun r => if r = 0 then a else if r = 5 then d else if r = 6 then flag else 0,
    fun _ => Scalar.zero, fun _ => none, fun _ => none, fun _ => none, []⟩

theorem inputState_bound (a d flag B : ℕ) (ha : a ≤ B) (hd : d ≤ B) (hf : flag ≤ B) :
    WordBound B (inputState a d flag) := by
  refine ⟨by simp [inputState], ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    simp only [inputState]
    split
    · exact ha
    · split
      · exact hd
      · split
        · exact hf
        · omega
  · simp [inputState]
  · simp [inputState]
  · simp [inputState]
  · simp [inputState]

theorem canonical_natural (a n : ℕ) (x : Fin n → ℂ) : ∃ u : State,
    BoundedExecution naturalProgram n x (a + 13) (inputState a 0 0)
      (5 + UniformPowerMachine.loopCost a) u ∧
      (u.scalarReg 0).value = (a : ℂ) ∧ (u.scalarReg 0).dependent = false ∧
      UniformPowerMachine.Frame (inputState a 0 0) u := by
  simpa [inputState] using bounded_natural_correct (a + 13) (by omega) (inputState a 0 0)
    (inputState_bound a 0 0 (a + 13) (by omega) (by omega) (by omega)) (by rfl) n x

theorem canonical_rational (a d n : ℕ) (hd : 0 < d) (x : Fin n → ℂ) : ∃ u : State,
    BoundedExecution rationalProgram n x (a + d + 29) (inputState a d 0)
      (13 + UniformPowerMachine.loopCost a + UniformPowerMachine.loopCost d) u ∧
      (u.scalarReg 2).value = (a : ℂ) / (d : ℂ) ∧ (u.scalarReg 2).dependent = false ∧
      RationalFrame (inputState a d 0) u := by
  simpa [inputState] using bounded_rational_correct (a + d + 29) (by omega) (inputState a d 0)
    (inputState_bound a d 0 (a + d + 29) (by omega) (by omega) (by omega)) (by rfl)
    (by simpa [inputState] using hd) n x

theorem canonical_signed (a d flag n : ℕ) (hd : 0 < d) (x : Fin n → ℂ) : ∃ u : State,
    BoundedExecution signedProgram n x (a + d + flag + 31) (inputState a d flag)
      (13 + UniformPowerMachine.loopCost a + UniformPowerMachine.loopCost d + signCost flag) u ∧
      (u.scalarReg 2).value = signedValue a d flag ∧ (u.scalarReg 2).dependent = false ∧
      RationalFrame (inputState a d flag) u := by
  simpa [inputState] using bounded_signed_correct (a + d + flag + 31) (by omega) (inputState a d flag)
    (inputState_bound a d flag (a + d + flag + 31) (by omega) (by omega) (by omega)) (by rfl)
    (by simpa [inputState] using hd) n x

end
end ExactFourierCircuits.UniformIntegerScalarMachine

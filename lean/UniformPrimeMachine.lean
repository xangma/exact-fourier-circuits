import UniformWorkingPreparation
import UniformAssembly

set_option autoImplicit false

namespace ExactFourierCircuits.UniformPrimeMachine
open UniformMachine
noncomputable section

/- Candidate=0, divisor=1, remaining fuel=2, zero=3, one=4, two=5,
   remainder=6, Boolean result=7. The program branches only on integers. -/
def program : Program :=
  [.natLiteral 3 0, .natLiteral 4 1, .natLiteral 5 2, .natLiteral 7 0,
   .branchLT 0 5 14 5, .natLiteral 1 2, .natBinary .sub 2 0 5,
   .branchLT 3 2 8 13, .natBinary .mod 6 0 1, .branchLT 3 6 10 14,
   .natBinary .add 1 1 4, .natBinary .sub 2 2 4, .jump 7,
   .natLiteral 7 1, .halt]

def boolCode (b : Bool) : ℕ := if b then 1 else 0

/-- Exact executed instruction counts, including the final halt. -/
def loopCost (p d : ℕ) : ℕ → ℕ
  | 0 => 3
  | f + 1 => if p % d = 0 then 4 else loopCost p (d + 1) f + 6

def totalCost (p : ℕ) : ℕ := if p < 2 then 6 else 7 + loopCost p 2 (p - 2)

def Frame (s u : State) : Prop :=
  u.natReg 0 = s.natReg 0 ∧ (∀ r, 8 ≤ r → u.natReg r = s.natReg r) ∧
    u.scalarReg = s.scalarReg ∧ u.natHeap = s.natHeap ∧
    u.scalarHeap = s.scalarHeap ∧ u.outputs = s.outputs ∧ u.rootOrders = s.rootOrders

theorem frame_refl (s : State) : Frame s s := ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Frame.trans {s u v : State} (h : Frame s u) (h' : Frame u v) : Frame s v := by
  obtain ⟨h0, hr, hs, hn, hh, ho, hd⟩ := h
  obtain ⟨h0', hr', hs', hn', hh', ho', hd'⟩ := h'
  exact ⟨h0'.trans h0, fun r h => (hr' r h).trans (hr r h), hs'.trans hs,
    hn'.trans hn, hh'.trans hh, ho'.trans ho, hd'.trans hd⟩

def initialized (s : State) : State :=
  writeNat (writeNat (writeNat (writeNat s 3 0) 4 1) 5 2) 7 0

def loopEntry (s : State) : State :=
  writeNat (writeNat { initialized s with pc := 5 } 1 2) 2 (s.natReg 0 - 2)

def Invariant (p d f : ℕ) (s : State) : Prop :=
  s.pc = 7 ∧ s.natReg 0 = p ∧ s.natReg 1 = d ∧ s.natReg 2 = f ∧
    s.natReg 3 = 0 ∧ s.natReg 4 = 1 ∧ s.natReg 5 = 2 ∧ s.natReg 7 = 0

def tested (s : State) : State := writeNat { s with pc := 8 } 6 (s.natReg 0 % s.natReg 1)
def incremented (s : State) : State :=
  writeNat { tested s with pc := 10 } 1 (s.natReg 1 + 1)
def decremented (s : State) : State := writeNat (incremented s) 2 (s.natReg 2 - 1)
def roundState (s : State) : State := { decremented s with pc := 7 }

theorem round_invariant (p d f : ℕ) (s : State) (hs : Invariant p d (f + 1) s) :
    Invariant p (d + 1) f (roundState s) := by
  obtain ⟨hp, h0, h1, h2, h3, h4, h5, h7⟩ := hs
  simp [Invariant, roundState, decremented, incremented, tested, writeNat, next,
    h0, h1, h2, h3, h4, h5, h7]

theorem state_frames (s : State) :
    Frame s (initialized s) ∧ Frame s (loopEntry s) ∧ Frame s (roundState s) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  all_goals first
  | solve | simp [initialized, loopEntry, roundState, decremented, incremented, tested, writeNat, next]
  | (intro r hr
     have h1 : r ≠ 1 := by omega
     have h2 : r ≠ 2 := by omega
     have h3 : r ≠ 3 := by omega
     have h4 : r ≠ 4 := by omega
     have h5 : r ≠ 5 := by omega
     have h6 : r ≠ 6 := by omega
     have h7 : r ≠ 7 := by omega
     simp [initialized, loopEntry, roundState, decremented, incremented, tested, writeNat,
       next, h1, h2, h3, h4, h5, h6, h7])

theorem round_bounded (B p d f n : ℕ) (x : Fin n → ℂ) (s : State)
    (hB : 15 ≤ B) (hs : Invariant p d (f + 1) s) (hb : WordBound B s)
    (hd : 0 < d) (hsum : d + (f + 1) ≤ p) (hm : p % d ≠ 0) :
    BoundedRuns program n x B s 6 (roundState s) := by
  obtain ⟨hp, h0, h1, h2, h3, h4, h5, h7⟩ := hs
  have hpb : p ≤ B := h0 ▸ hb.2.1 0
  have hrem : p % d ≤ B := le_trans (Nat.le_of_lt (Nat.mod_lt _ hd)) (by omega)
  have htest : WordBound B (tested s) := writeNat_bound _ _ 6 _
    (changePC_bound _ s 8 hb (by omega)) (by simp; omega) (by simpa [h0, h1] using hrem)
  have hinc : WordBound B (incremented s) := writeNat_bound _ _ 1 _
    (changePC_bound _ (tested s) 10 htest (by omega)) (by simp; omega) (by omega)
  have hdec : WordBound B (decremented s) := writeNat_bound _ _ 2 _ hinc
    (by simp [incremented, writeNat, next]; omega) (by simpa [h2] using (by omega : f + 1 - 1 ≤ B))
  have hround : WordBound B (roundState s) := changePC_bound _ _ 7 hdec (by omega)
  refine .next hb (u := { s with pc := 8 }) ?_
    (.next (changePC_bound _ s 8 hb (by omega)) (u := tested s) ?_
      (.next htest (u := { tested s with pc := 10 }) ?_
        (.next (changePC_bound _ _ 10 htest (by omega)) (u := incremented s) ?_
          (.next hinc (u := decremented s) ?_ (.next hdec (u := roundState s) ?_ (.refl hround))))))
  all_goals simp [step, program, evalNat, roundState, decremented, incremented, tested,
    writeNat, next, hp, h0, h1, h2, h3, h4, hd.ne', Nat.pos_of_ne_zero hm]

theorem loop_bounded (B p d f n : ℕ) (x : Fin n → ℂ) (s : State)
    (hB : 15 ≤ B) (hs : Invariant p d f s) (hb : WordBound B s)
    (hd : 0 < d) (hsum : d + f ≤ p) : ∃ u : State,
    BoundedExecution program n x B s (loopCost p d f) u ∧ u.pc = 14 ∧
      u.natReg 7 = boolCode (UniformWorkingPreparation.trialLoop p d f).value ∧ Frame s u := by
  induction f generalizing d s with
  | zero =>
    obtain ⟨hp, h0, h1, h2, h3, h4, h5, h7⟩ := hs
    let u := writeNat { s with pc := 13 } 7 1
    have hu : WordBound B u := writeNat_bound _ _ 7 1
      (changePC_bound _ s 13 hb (by omega)) (by simp; omega) (by omega)
    refine ⟨u, .next hb (u := { s with pc := 13 }) ?_
      (.next (changePC_bound _ s 13 hb (by omega)) (u := u) ?_ (.halt hu ?_)),
      rfl, ?_, ?_⟩
    · simp [step, program, hp, h2, h3]
    · simp [step, program, u]
    · simp [step, program, u, writeNat, next]
    · simp [u, writeNat, boolCode, UniformWorkingPreparation.trialLoop]
    · refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
      · simp [u, writeNat, next]
      · intro r hr; simp [u, writeNat, next, show r ≠ 7 by omega]
  | succ f ih =>
    by_cases hm : p % d = 0
    · obtain ⟨hp, h0, h1, h2, h3, h4, h5, h7⟩ := hs
      have ht : WordBound B (tested s) := writeNat_bound _ _ 6 _
        (changePC_bound _ s 8 hb (by omega)) (by simp; omega) (by simp [h0, h1, hm])
      let u := { tested s with pc := 14 }
      refine ⟨u, ?_, rfl, ?_, ?_⟩
      · rw [loopCost, ite_eq_left hm]
        refine .next hb (u := { s with pc := 8 }) ?_
          (.next (changePC_bound _ s 8 hb (by omega)) (u := tested s) ?_
            (.next ht (u := u) ?_ (.halt (changePC_bound _ _ 14 ht (by omega)) ?_)))
        all_goals simp [step, program, evalNat, u, tested, writeNat, next,
          hp, h0, h1, h2, h3, hd.ne', hm]
      · simp [u, tested, writeNat, h7, boolCode, UniformWorkingPreparation.trialLoop, hm]
      · refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
        · simp [u, tested, writeNat, next]
        · intro r hr; simp [u, tested, writeNat, next, show r ≠ 6 by omega]
    · have hr := round_bounded B p d f n x s hB hs hb hd hsum hm
      obtain ⟨u, hu, hpc, hresult, hframe⟩ := ih (d + 1) (roundState s)
        (round_invariant p d f s hs) hr.final_bound (by omega) (by omega)
      refine ⟨u, ?_, hpc, ?_, (state_frames s).2.2.trans hframe⟩
      · rw [loopCost, ite_eq_right hm]
        simpa only [Nat.add_comm] using hr.executes hu
      · simpa [UniformWorkingPreparation.trialLoop, hm] using hresult

theorem loopCost_bound (p d f : ℕ) : loopCost p d f ≤ 6 * f + 4 := by
  induction f generalizing d with
  | zero => simp [loopCost]
  | succ f ih =>
    by_cases hm : p % d = 0
    · simp [loopCost, hm]
    · simp only [loopCost, hm, ite_false]
      have hi := ih (d + 1)
      omega

theorem initialized_bounded (B n : ℕ) (x : Fin n → ℂ) (s : State)
    (hB : 15 ≤ B) (hp : s.pc = 0) (hb : WordBound B s) :
    BoundedRuns program n x B s 4 (initialized s) := by
  have h1 := writeNat_bound B s 3 0 hb (by omega) (by omega)
  have h2 := writeNat_bound B (writeNat s 3 0) 4 1 h1
    (by simp [writeNat, next, hp]; omega) (by omega)
  have h3 := writeNat_bound B (writeNat (writeNat s 3 0) 4 1) 5 2 h2
    (by simp [writeNat, next, hp]; omega) (by omega)
  have h4 := writeNat_bound B (writeNat (writeNat (writeNat s 3 0) 4 1) 5 2) 7 0 h3
    (by simp [writeNat, next, hp]; omega) (by omega)
  refine .next hb (u := writeNat s 3 0) ?_
    (.next h1 (u := writeNat (writeNat s 3 0) 4 1) ?_
      (.next h2 (u := writeNat (writeNat (writeNat s 3 0) 4 1) 5 2) ?_
        (.next h3 (u := initialized s) ?_ (.refl h4))))
  all_goals simp [step, program, initialized, writeNat, next, hp]

theorem start_bounded (B n : ℕ) (x : Fin n → ℂ) (s : State)
    (hB : 15 ≤ B) (hp : s.pc = 0) (hb : WordBound B s) (hsmall : ¬s.natReg 0 < 2) :
    BoundedRuns program n x B s 7 (loopEntry s) := by
  have hr := initialized_bounded B n x s hB hp hb
  have h5 := changePC_bound B (initialized s) 5 hr.final_bound (by omega)
  have h6 := writeNat_bound B { initialized s with pc := 5 } 1 2 h5 (by simp; omega) (by omega)
  have h7 := writeNat_bound B (writeNat { initialized s with pc := 5 } 1 2) 2
    (s.natReg 0 - 2) h6 (by simp [writeNat, next]; omega)
    (le_trans (Nat.sub_le _ _) (hb.2.1 0))
  have he : BoundedRuns program n x B (initialized s) 3 (loopEntry s) := by
    refine .next hr.final_bound (u := { initialized s with pc := 5 }) ?_
      (.next h5 (u := writeNat { initialized s with pc := 5 } 1 2) ?_
        (.next h6 (u := loopEntry s) ?_ (.refl h7)))
    all_goals simp [step, program, evalNat, loopEntry, initialized, writeNat, next, hp, hsmall]
  exact hr.trans he

theorem loopEntry_invariant (s : State) :
    Invariant (s.natReg 0) 2 (s.natReg 0 - 2) (loopEntry s) := by
  simp [Invariant, loopEntry, initialized, writeNat, next]

/-- Literal fixed-program execution agrees with the computable trial-division function.
    Existing initialized memory and prepared or dependent scalar registers are preserved. -/
theorem bounded_trialPrime (B n : ℕ) (x : Fin n → ℂ) (s : State)
    (hB : 15 ≤ B) (hp : s.pc = 0) (hb : WordBound B s) : ∃ u : State,
    BoundedExecution program n x B s (totalCost (s.natReg 0)) u ∧ u.pc = 14 ∧
      u.natReg 7 = boolCode (UniformWorkingPreparation.trialPrime (s.natReg 0)).value ∧
      Frame s u := by
  by_cases hsmall : s.natReg 0 < 2
  · have hr := initialized_bounded B n x s hB hp hb
    let u := { initialized s with pc := 14 }
    have he : BoundedExecution program n x B (initialized s) 2 u := by
      refine .next hr.final_bound (u := u) ?_
        (.halt (changePC_bound _ _ 14 hr.final_bound (by omega)) ?_)
      all_goals simp [step, program, u, initialized, writeNat, next, hp, hsmall]
    refine ⟨u, ?_, rfl, ?_, ?_⟩
    · simpa [totalCost, hsmall] using hr.executes he
    · simp [u, initialized, writeNat, boolCode, UniformWorkingPreparation.trialPrime, hsmall]
    · exact (state_frames s).1
  · have hr := start_bounded B n x s hB hp hb hsmall
    obtain ⟨u, hu, hpc, hv, hf⟩ := loop_bounded B (s.natReg 0) 2 (s.natReg 0 - 2)
      n x (loopEntry s) hB (loopEntry_invariant s) hr.final_bound (by decide) (by omega)
    refine ⟨u, ?_, hpc, ?_, (state_frames s).2.1.trans hf⟩
    · simpa [totalCost, hsmall] using hr.executes hu
    · simpa [UniformWorkingPreparation.trialPrime, hsmall] using hv

theorem boolCode_one (b : Bool) : boolCode b = 1 ↔ b = true := by cases b <;> decide

theorem bounded_prime_correct (B n : ℕ) (x : Fin n → ℂ) (s : State)
    (hB : 15 ≤ B) (hp : s.pc = 0) (hb : WordBound B s) : ∃ u : State,
    BoundedExecution program n x B s (totalCost (s.natReg 0)) u ∧ u.pc = 14 ∧
      (u.natReg 7 = 1 ↔ Nat.Prime (s.natReg 0)) ∧
      (u.natReg 7 = 0 ∨ u.natReg 7 = 1) ∧ Frame s u := by
  obtain ⟨u, hu, hpc, hv, hf⟩ := bounded_trialPrime B n x s hB hp hb
  refine ⟨u, hu, hpc, ?_, ?_, hf⟩
  · rw [hv, boolCode_one, UniformWorkingPreparation.trialPrime_true]
  · rw [hv]; cases (UniformWorkingPreparation.trialPrime (s.natReg 0)).value <;> simp [boolCode]

theorem totalCost_bound (p : ℕ) : totalCost p ≤ 6 * p + 11 := by
  by_cases hp : p < 2
  · simp [totalCost, hp]
  · simp only [totalCost, hp, ite_false]
    have h := loopCost_bound p 2 (p - 2)
    omega

def candidateState (p : ℕ) : State := { initial with natReg := Function.update initial.natReg 0 p }

theorem candidateState_bound (p : ℕ) : WordBound (p + 15) (candidateState p) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [candidateState, initial]
  · intro r; by_cases hr : r = 0 <;> simp [candidateState, initial, hr]
  · simp [candidateState, initial]
  · simp [candidateState, initial]
  · simp [candidateState, initial]
  · simp [candidateState, initial]

/-- Closed prepared-candidate entry point; it requests no roots and reads no inputs. -/
theorem canonical_prime (p n : ℕ) (x : Fin n → ℂ) : ∃ u : State,
    BoundedExecution program n x (p + 15) (candidateState p) (totalCost p) u ∧ u.pc = 14 ∧
      (u.natReg 7 = 1 ↔ Nat.Prime p) ∧ (u.natReg 7 = 0 ∨ u.natReg 7 = 1) ∧
      Frame (candidateState p) u := by
  simpa [candidateState, initial] using bounded_prime_correct (p + 15) n x (candidateState p)
    (by omega) rfl (candidateState_bound p)

/-- Relocating this literal helper replaces its halt by a charged continuation jump.
    It introduces no oracle, call primitive, extra roots, or uncharged control transfer. -/
theorem placed_trialPrime (q : Program) (base returnPC B C n : ℕ) (x : Fin n → ℂ)
    (code : UniformAssembly.CodeAt program q base returnPC) (hBC : base + B ≤ C)
    (hret : returnPC ≤ C) (s : State) (hB : 15 ≤ B) (hp : s.pc = 0)
    (hb : WordBound B s) : ∃ u : State,
    BoundedRuns q n x C (UniformAssembly.placed base s) (totalCost (s.natReg 0)) u ∧
      u.pc = returnPC ∧
      u.natReg 7 = boolCode (UniformWorkingPreparation.trialPrime (s.natReg 0)).value ∧
      Frame (UniformAssembly.placed base s) u := by
  obtain ⟨u, hu, _, hv, hf⟩ := bounded_trialPrime B n x s hB hp hb
  exact ⟨{ u with pc := returnPC }, UniformAssembly.BoundedExecution.placed code hBC hret hu,
    rfl, hv, hf⟩

end
end ExactFourierCircuits.UniformPrimeMachine

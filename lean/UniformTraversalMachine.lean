import UniformMachine
import UniformTraversal

set_option autoImplicit false

namespace ExactFourierCircuits.UniformTraversalMachine
open UniformMachine UniformTraversal

/- Fixed register interface: S,Q,o,I,p,q,t,r,a,tau,tmp = 0,...,10.
   This program contains only eight charged integer instructions and a halt. -/
def program : Program :=
  [.natBinary .mul 10 1 4, .natBinary .mul 10 10 9, .natBinary .add 0 0 10,
   .natBinary .mul 1 1 5, .natBinary .mul 2 2 5, .natBinary .add 2 2 6,
   .natBinary .mul 3 3 7, .natBinary .add 3 3 8, .halt]

def packingState (s : State) : PackingState := ⟨s.natReg 0, s.natReg 1, s.natReg 2, s.natReg 3⟩
def packingDigit (s : State) : PackingDigit :=
  ⟨s.natReg 7, s.natReg 9, s.natReg 4, s.natReg 5, s.natReg 6, s.natReg 8⟩

def stage1 (s : State) : State := writeNat s 10 (s.natReg 1 * s.natReg 4)
def stage2 (s : State) : State := writeNat (stage1 s) 10 (s.natReg 1 * s.natReg 4 * s.natReg 9)
def stage3 (s : State) : State := writeNat (stage2 s) 0 (s.natReg 0 + s.natReg 1 * s.natReg 4 * s.natReg 9)
def stage4 (s : State) : State := writeNat (stage3 s) 1 (s.natReg 1 * s.natReg 5)
def stage5 (s : State) : State := writeNat (stage4 s) 2 (s.natReg 2 * s.natReg 5)
def stage6 (s : State) : State := writeNat (stage5 s) 2 (s.natReg 2 * s.natReg 5 + s.natReg 6)
def stage7 (s : State) : State := writeNat (stage6 s) 3 (s.natReg 3 * s.natReg 7)
def finalState (s : State) : State := writeNat (stage7 s) 3 (s.natReg 3 * s.natReg 7 + s.natReg 8)

theorem program_length : program.length = 9 := rfl

/-- Actual instruction semantics, for every input array and any incoming prepared tables. -/
theorem executes (s : State) (hpc : s.pc = 0) (n : ℕ) (x : Fin n → ℂ) :
    Executes program n x s 9 (finalState s) := by
  refine .next (u := stage1 s) ?_ (.next (u := stage2 s) ?_
    (.next (u := stage3 s) ?_ (.next (u := stage4 s) ?_
      (.next (u := stage5 s) ?_ (.next (u := stage6 s) ?_
        (.next (u := stage7 s) ?_ (.next (u := finalState s) ?_ (.halt ?_))))))))
  all_goals simp [step, program, evalNat, stage1, stage2, stage3, stage4, stage5, stage6,
    stage7, finalState, writeNat, next, hpc]

theorem executes_unique (s : State) (hpc : s.pc = 0) (n : ℕ) (x : Fin n → ℂ)
    (t : ℕ) (u : State) (he : Executes program n x s t u) : t = 9 ∧ u = finalState s :=
  he.deterministic (executes s hpc n x)

theorem final_packingState (s : State) :
    packingState (finalState s) = packingStep (packingDigit s) (packingState s) := by
  simp [packingState, packingDigit, packingStep, stage1, stage2, stage3, stage4, stage5,
    stage6, stage7, finalState, writeNat, next]

theorem final_temporary (s : State) :
    (finalState s).natReg 10 = s.natReg 1 * s.natReg 4 * s.natReg 9 := by
  simp [stage1, stage2, stage3, stage4, stage5, stage6, stage7, finalState, writeNat, next]

theorem final_natReg_other (s : State) (r : ℕ)
    (h0 : r ≠ 0) (h1 : r ≠ 1) (h2 : r ≠ 2) (h3 : r ≠ 3) (h10 : r ≠ 10) :
    (finalState s).natReg r = s.natReg r := by
  simp [stage1, stage2, stage3, stage4, stage5, stage6, stage7, finalState, writeNat, next,
    h0, h1, h2, h3, h10]

theorem final_pc (s : State) : (finalState s).pc = s.pc + 8 := by
  simp [stage1, stage2, stage3, stage4, stage5, stage6, stage7, finalState, writeNat, next]

theorem final_preserves_auxiliary_state (s : State) :
    (finalState s).scalarReg = s.scalarReg ∧ (finalState s).natHeap = s.natHeap ∧
      (finalState s).scalarHeap = s.scalarHeap ∧ (finalState s).outputs = s.outputs ∧
        (finalState s).rootOrders = s.rootOrders := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem writeNat_wordBound (B : ℕ) (s : State) (r value : ℕ)
    (hs : WordBound B s) (hpc : s.pc + 1 ≤ B) (hv : value ≤ B) :
    WordBound B (writeNat s r value) := by
  obtain ⟨_, hreg, hnat, hscalar, hout, hroot⟩ := hs
  refine ⟨hpc, ?_, hnat, hscalar, hout, hroot⟩
  intro j
  by_cases hj : j = r
  · subst j
    simpa [writeNat, next] using hv
  · simpa [writeNat, next, hj] using hreg j

/-- Geometric prefix invariants and prepared local-table bounds, expressed in incoming registers. -/
def LocalBounds (s : State) (R P : ℕ) : Prop :=
  let st := packingState s
  let d := packingDigit s
  st.start + st.width * (d.radix * d.suffix) ≤ R ∧ st.offset < st.width ∧ st.original < P ∧
    d.preceding + d.blockWidth ≤ d.radix ∧ d.position < d.blockWidth ∧
      d.originalDigit < d.radix ∧ 0 < d.suffix ∧ P * d.radix ≤ R

def AssignmentBounds (s : State) (R : ℕ) : Prop :=
  s.natReg 1 * s.natReg 4 ≤ R ∧
    s.natReg 1 * s.natReg 4 * s.natReg 9 ≤ R ∧
    s.natReg 0 + s.natReg 1 * s.natReg 4 * s.natReg 9 ≤ R ∧
    s.natReg 1 * s.natReg 5 ≤ R ∧
    s.natReg 2 * s.natReg 5 ≤ R ∧
    s.natReg 2 * s.natReg 5 + s.natReg 6 ≤ R ∧
    s.natReg 3 * s.natReg 7 ≤ R ∧
    s.natReg 3 * s.natReg 7 + s.natReg 8 ≤ R

/-- Every written temporary and updated address fits the same array-size bound. -/
theorem assignment_bounds (s : State) (R P : ℕ) (hv : LocalBounds s R P) : AssignmentBounds s R := by
  obtain ⟨hfit, ho, hI, hpq, ht, ha, htau, hPR⟩ := hv
  let Q := s.natReg 1
  let p := s.natReg 4
  let q := s.natReg 5
  let tau := s.natReg 9
  let r := s.natReg 7
  change s.natReg 0 + Q * (r * tau) ≤ R at hfit
  change p + q ≤ r at hpq
  change 0 < tau at htau
  have hfull : Q * (r * tau) ≤ R := by omega
  have htmp : Q * p * tau ≤ Q * (r * tau) := by
    calc
      _ ≤ Q * r * tau := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
      _ = _ := Nat.mul_assoc _ _ _
  have hv2 : Q * p * tau ≤ R := htmp.trans hfull
  have hv1 : Q * p ≤ R := by
    have hsmall : Q * p ≤ Q * p * tau := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (Q * p) (show 1 ≤ tau by omega)
    exact hsmall.trans hv2
  have hv3 : s.natReg 0 + Q * p * tau ≤ R :=
    (Nat.add_le_add_left htmp _).trans hfit
  have hv4 : Q * q ≤ R := by
    have hqt : Q * q * tau ≤ Q * (r * tau) := by
      calc
        _ ≤ Q * r * tau := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
        _ = _ := Nat.mul_assoc _ _ _
    have hsmall : Q * q ≤ Q * q * tau := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (Q * q) (show 1 ≤ tau by omega)
    exact hsmall.trans (hqt.trans hfull)
  have hv5 : s.natReg 2 * q ≤ R :=
    (Nat.mul_le_mul_right _ (show s.natReg 2 ≤ Q by exact Nat.le_of_lt ho)).trans hv4
  have hv6 : s.natReg 2 * q + s.natReg 6 ≤ R :=
    (packingStep_offset_bound (packingDigit s) (packingState s) ho ht).le.trans hv4
  have hv7 : s.natReg 3 * r ≤ R :=
    (Nat.mul_le_mul_right _ (show s.natReg 3 ≤ P by exact Nat.le_of_lt hI)).trans hPR
  have hv8 : s.natReg 3 * r + s.natReg 8 ≤ R :=
    (packingStep_original_bound (packingDigit s) (packingState s) P hI ha).le.trans hPR
  exact ⟨hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8⟩

/-- The actual nine-instruction execution bounds every intermediate RAM state.
    Eight extra units suffice for the fixed program counter. Heaps and tables stay untouched. -/
theorem bounded_executes (s : State) (hpc : s.pc = 0) (n : ℕ) (x : Fin n → ℂ)
    (R P : ℕ) (hs : WordBound (R + 8) s) (hv : LocalBounds s R P) :
    BoundedExecution program n x (R + 8) s 9 (finalState s) := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := assignment_bounds s R P hv
  have h1 : WordBound (R + 8) (stage1 s) :=
    writeNat_wordBound _ _ _ _ hs (by omega) (by omega)
  have h2 : WordBound (R + 8) (stage2 s) :=
    writeNat_wordBound _ _ _ _ h1 (by change s.pc + 2 ≤ R + 8; omega) (by omega)
  have h3 : WordBound (R + 8) (stage3 s) :=
    writeNat_wordBound _ _ _ _ h2 (by change s.pc + 3 ≤ R + 8; omega) (by omega)
  have h4 : WordBound (R + 8) (stage4 s) :=
    writeNat_wordBound _ _ _ _ h3 (by change s.pc + 4 ≤ R + 8; omega) (by omega)
  have h5 : WordBound (R + 8) (stage5 s) :=
    writeNat_wordBound _ _ _ _ h4 (by change s.pc + 5 ≤ R + 8; omega) (by omega)
  have h6 : WordBound (R + 8) (stage6 s) :=
    writeNat_wordBound _ _ _ _ h5 (by change s.pc + 6 ≤ R + 8; omega) (by omega)
  have h7 : WordBound (R + 8) (stage7 s) :=
    writeNat_wordBound _ _ _ _ h6 (by change s.pc + 7 ≤ R + 8; omega) (by omega)
  have h8 : WordBound (R + 8) (finalState s) :=
    writeNat_wordBound _ _ _ _ h7 (by change s.pc + 8 ≤ R + 8; omega) (by omega)
  refine .next hs ?_ (.next h1 ?_ (.next h2 ?_ (.next h3 ?_ (.next h4 ?_
    (.next h5 ?_ (.next h6 ?_ (.next h7 ?_ (.halt h8 ?_))))))))
  all_goals simp [step, program, evalNat, stage1, stage2, stage3, stage4, stage5, stage6,
    stage7, finalState, writeNat, next, hpc]

end ExactFourierCircuits.UniformTraversalMachine

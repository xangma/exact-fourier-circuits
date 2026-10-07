import UniformMachineRuns

set_option autoImplicit false

/- The bounded-length fallback needed by the paper. This finite RAM program
   computes the ordinary DFT directly. Its quadratic count does not establish
   the stronger saving bound. Coefficients use one supplied root and successive
   products; all data products have a prepared operand. -/
namespace ExactFourierCircuits.UniformDirectMachine
noncomputable section
open UniformMachine OAI.ExactFourier
open scoped BigOperators

/-- Nat: n=0,k=1,j=2,one=3. Scalar: root=0,row=1,power=2,sum=3,input=4,term=5. -/
def program : Program :=
  [.length 0, .natLiteral 3 1, .root 0 0, .natLiteral 1 0, .scalarLiteral 1 1,
   .branchLT 1 0 6 20, .natLiteral 2 0, .scalarLiteral 2 1, .scalarLiteral 3 0,
   .branchLT 2 0 10 16, .input 4 2, .fieldBinary .mul 5 2 4,
   .fieldBinary .add 3 3 5, .fieldBinary .mul 2 2 1,
   .natBinary .add 2 2 3, .jump 9, .output 1 3,
   .fieldBinary .mul 1 1 0, .natBinary .add 1 1 3, .jump 5, .halt]

def term {n : ℕ} (x : Fin n → ℂ) (k j : ℕ) : ℂ :=
  if h : j < n then zeta n ^ (k * j) * x ⟨j, h⟩ else 0

def partialSum {n : ℕ} (x : Fin n → ℂ) (k j : ℕ) : ℂ := ∑ l ∈ Finset.range j, term x k l

theorem partialSum_zero {n : ℕ} (x : Fin n → ℂ) (k : ℕ) : partialSum x k 0 = 0 := by
  simp [partialSum]

theorem partialSum_succ {n : ℕ} (x : Fin n → ℂ) (k j : ℕ) (hj : j < n) :
    partialSum x k (j + 1) = partialSum x k j + zeta n ^ (k * j) * x ⟨j, hj⟩ := by
  simp [partialSum, Finset.sum_range_succ, term, hj]

theorem partialSum_dft {n : ℕ} (x : Fin n → ℂ) (k : Fin n) :
    partialSum x k.val n = (fourierMatrix n).mulVec x k := by
  rw [partialSum, ← Fin.sum_univ_eq_sum_range]
  simp [term, Matrix.mulVec, dotProduct, fourierMatrix]

def context {n : ℕ} (k : ℕ) (s : State) : Prop :=
  s.natReg 0 = n ∧ s.natReg 1 = k ∧ s.natReg 3 = 1 ∧
  s.scalarReg 0 = ⟨zeta n, false⟩ ∧ s.scalarReg 1 = ⟨zeta n ^ k, false⟩ ∧
  s.rootOrders = [n]

def innerInvariant {n : ℕ} (x : Fin n → ℂ) (k j : ℕ) (s : State) : Prop :=
  context (n := n) k s ∧ s.pc = 9 ∧ s.natReg 2 = j ∧
  s.scalarReg 2 = ⟨zeta n ^ (k * j), false⟩ ∧ (s.scalarReg 3).value = partialSum x k j

def readState {n : ℕ} (x : Fin n → ℂ) (j : Fin n) (s : State) : State :=
  writeScalar { s with pc := 10 } 4 ⟨x j, true⟩

def multiplyState {n : ℕ} (x : Fin n → ℂ) (k : ℕ) (j : Fin n) (s : State) : State :=
  writeScalar (readState x j s) 5 ⟨zeta n ^ (k * j.val) * x j, true⟩

def addState {n : ℕ} (x : Fin n → ℂ) (k : ℕ) (j : Fin n) (s : State) : State :=
  writeScalar (multiplyState x k j s) 3 ⟨partialSum x k (j.val + 1), true⟩

def powerState {n : ℕ} (x : Fin n → ℂ) (k : ℕ) (j : Fin n) (s : State) : State :=
  writeScalar (addState x k j s) 2 ⟨zeta n ^ (k * (j.val + 1)), false⟩

def innerNext {n : ℕ} (x : Fin n → ℂ) (k : ℕ) (j : Fin n) (s : State) : State :=
  { writeNat (powerState x k j s) 2 (j.val + 1) with pc := 9 }

theorem inner_round {n : ℕ} (x : Fin n → ℂ) (k : ℕ) (j : Fin n) (s : State)
    (hs : innerInvariant x k j.val s) : Runs program n x s 7 (innerNext x k j s) := by
  obtain ⟨⟨hn, hk, h1, hroot, hrow, _⟩, hpc, hj, hp, ha⟩ := hs
  refine .next (u := { s with pc := 10 }) ?_ (.next (u := readState x j s) ?_
    (.next (u := multiplyState x k j s) ?_ (.next (u := addState x k j s) ?_
      (.next (u := powerState x k j s) ?_
        (.next (u := writeNat (powerState x k j s) 2 (j.val + 1)) ?_
          (.next (u := innerNext x k j s) ?_ (.refl _)))))))
  · simp [step, program, hpc, hj, hn, j.isLt]
  · simp [step, program, hj, readState, j.isLt]
  · simp [step, program, readState, writeScalar, next, hp, evalField, multiplyState]
  · simp [step, program, multiplyState, readState, writeScalar, next, ha, evalField,
      addState, partialSum_succ x k j.val j.isLt]
  · simp [step, program, addState, multiplyState, readState, writeScalar, next, hp,
      hrow, evalField, powerState]
    rw [← pow_add, Nat.mul_add, Nat.mul_one]
  · simp [step, program, powerState, addState, multiplyState, readState, writeScalar,
      next, hj, h1, evalNat]
  · simp [step, program, powerState, addState, multiplyState, readState, writeScalar,
      writeNat, next, innerNext]

theorem inner_round_invariant {n : ℕ} (x : Fin n → ℂ) (k : ℕ) (j : Fin n) (s : State)
    (hs : innerInvariant x k j.val s) : innerInvariant x k (j.val + 1) (innerNext x k j s) := by
  obtain ⟨⟨hn, hk, h1, hroot, hrow, hr⟩, _, _, _, _⟩ := hs
  simp [innerInvariant, context, innerNext, powerState, addState, multiplyState,
    readState, writeScalar, writeNat, next, hn, hk, h1, hroot, hrow, hr]

theorem inner_round_outputs {n : ℕ} (x : Fin n → ℂ) (k : ℕ) (j : Fin n) (s : State) :
    (innerNext x k j s).outputs = s.outputs := rfl

theorem inner_loop {n : ℕ} (x : Fin n → ℂ) (k f j : ℕ) (s : State)
    (hj : j + f = n) (hs : innerInvariant x k j s) :
    ∃ u, Runs program n x s (7 * f) u ∧ innerInvariant x k n u ∧ u.outputs = s.outputs := by
  induction f generalizing j s with
  | zero =>
      have hjn : j = n := by omega
      subst j
      exact ⟨s, by simpa using Runs.refl s, hs, rfl⟩
  | succ f ih =>
      have hjn : j < n := by omega
      let jj : Fin n := ⟨j, hjn⟩
      obtain ⟨u, hu, hi, ho⟩ := ih (j + 1) (innerNext x k jj s) (by omega)
        (inner_round_invariant x k jj s hs)
      refine ⟨u, ?_, hi, ho.trans (inner_round_outputs x k jj s)⟩
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_comm] using
        (inner_round x k jj s hs).trans hu

def outerInvariant {n : ℕ} (x : Fin n → ℂ) (k : ℕ) (s : State) : Prop :=
  context (n := n) k s ∧ s.pc = 5 ∧
    ∀ l : Fin n, l.val < k → s.outputs l.val = some ((fourierMatrix n).mulVec x l)

def innerInitial (s : State) : State :=
  writeScalar (writeScalar (writeNat { s with pc := 6 } 2 0) 2 ⟨1, false⟩) 3 ⟨0, false⟩

theorem enter_row {n : ℕ} (x : Fin n → ℂ) (k : Fin n) (s : State)
    (hs : outerInvariant x k.val s) : Runs program n x s 4 (innerInitial s) := by
  obtain ⟨⟨hn, hk, _, _, _, _⟩, hp, _⟩ := hs
  refine .next (u := { s with pc := 6 }) ?_
    (.next (u := writeNat { s with pc := 6 } 2 0) ?_
      (.next (u := writeScalar (writeNat { s with pc := 6 } 2 0) 2 ⟨1, false⟩) ?_
        (.next (u := innerInitial s) ?_ (.refl _))))
  all_goals simp [step, program, hp, hk, hn, k.isLt, writeNat, writeScalar, next, innerInitial]

theorem innerInitial_invariant {n : ℕ} (x : Fin n → ℂ) (k : ℕ) (s : State)
    (hs : outerInvariant x k s) : innerInvariant x k 0 (innerInitial s) := by
  obtain ⟨⟨hn, hk, h1, hr, hw, hroots⟩, _, _⟩ := hs
  simp [innerInvariant, context, innerInitial, writeNat, writeScalar, next,
    hn, hk, h1, hr, hw, hroots, partialSum_zero]

def emitState (s : State) : State :=
  { s with pc := 17, outputs := Function.update s.outputs (s.natReg 1) (some (s.scalarReg 3).value) }

def nextRow {n : ℕ} (k : ℕ) (s : State) : State :=
  { writeNat (writeScalar (emitState s) 1 ⟨zeta n ^ (k + 1), false⟩) 1 (k + 1) with pc := 5 }

theorem finish_row {n : ℕ} (x : Fin n → ℂ) (k : Fin n) (s : State)
    (hs : innerInvariant x k.val n s) : Runs program n x s 5 (nextRow (n := n) k.val s) := by
  obtain ⟨⟨hn, hk, h1, hr, hw, _⟩, hp, hj, _, _⟩ := hs
  refine .next (u := { s with pc := 16 }) ?_ (.next (u := emitState s) ?_
    (.next (u := writeScalar (emitState s) 1 ⟨zeta n ^ (k.val + 1), false⟩) ?_
      (.next (u := writeNat (writeScalar (emitState s) 1 ⟨zeta n ^ (k.val + 1), false⟩) 1 (k.val + 1)) ?_
        (.next (u := nextRow (n := n) k.val s) ?_ (.refl _)))))
  · simp [step, program, hp, hj, hn]
  · simp [step, program, hk, k.isLt, emitState, next]
  · simp [step, program, emitState, hw, hr, evalField, writeScalar]
    rw [pow_succ]
  · simp [step, program, emitState, writeScalar, next, hk, h1, evalNat]
  · simp [step, program, emitState, writeScalar, writeNat, next, nextRow]

theorem nextRow_invariant {n : ℕ} (x : Fin n → ℂ) (k : Fin n) (s : State)
    (hs : innerInvariant x k.val n s)
    (ho : ∀ l : Fin n, l.val < k.val → s.outputs l.val = some ((fourierMatrix n).mulVec x l)) :
    outerInvariant x (k.val + 1) (nextRow (n := n) k.val s) := by
  obtain ⟨⟨hn, hk, h1, hr, _, hroots⟩, _, _, _, ha⟩ := hs
  refine ⟨?_, rfl, ?_⟩
  · simp [context, nextRow, emitState, writeNat, writeScalar, next, hn, h1, hr, hroots]
  · intro l hl
    by_cases h : l.val = k.val
    · have he : l = k := Fin.ext h
      subst l
      simp [nextRow, emitState, writeNat, writeScalar, next, hk, ha, partialSum_dft]
    · have hlt : l.val < k.val := by omega
      simpa [nextRow, emitState, writeNat, writeScalar, next, hk, h] using ho l hlt

theorem outer_round {n : ℕ} (x : Fin n → ℂ) (k : Fin n) (s : State)
    (hs : outerInvariant x k.val s) :
    ∃ u, Runs program n x s (7 * n + 9) u ∧ outerInvariant x (k.val + 1) u := by
  obtain ⟨v, hv, hi, ho⟩ := inner_loop x k.val n 0 (innerInitial s) (by omega)
    (innerInitial_invariant x k.val s hs)
  refine ⟨nextRow (n := n) k.val v, ?_, nextRow_invariant x k v hi ?_⟩
  · convert ((enter_row x k s hs).trans hv).trans (finish_row x k v hi) using 1; omega
  · intro l hl
    rw [ho]
    exact hs.2.2 l hl

theorem outer_loop {n : ℕ} (x : Fin n → ℂ) (f k : ℕ) (s : State)
    (hk : k + f = n) (hs : outerInvariant x k s) :
    ∃ u, Runs program n x s ((7 * n + 9) * f) u ∧ outerInvariant x n u := by
  induction f generalizing k s with
  | zero =>
      have hkn : k = n := by omega
      subst k
      exact ⟨s, by simpa using Runs.refl s, hs⟩
  | succ f ih =>
      have hkn : k < n := by omega
      let kk : Fin n := ⟨k, hkn⟩
      obtain ⟨v, hv, hi⟩ := outer_round x kk s hs
      obtain ⟨u, hu, hiu⟩ := ih (k + 1) v (by omega) hi
      refine ⟨u, ?_, hiu⟩
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_comm] using hv.trans hu

def startupRoot (n : ℕ) : State :=
  { writeScalar (writeNat (writeNat initial 0 n) 3 1) 0 ⟨zeta n, false⟩ with rootOrders := [n] }

def startup (n : ℕ) : State := writeScalar (writeNat (startupRoot n) 1 0) 1 ⟨1, false⟩

theorem startup_runs {n : ℕ} (hn : 0 < n) (x : Fin n → ℂ) :
    Runs program n x initial 5 (startup n) := by
  refine .next (u := writeNat initial 0 n) ?_ (.next (u := writeNat (writeNat initial 0 n) 3 1) ?_
    (.next (u := startupRoot n) ?_ (.next (u := writeNat (startupRoot n) 1 0) ?_
      (.next (u := startup n) ?_ (.refl _)))))
  all_goals simp [step, program, initial, writeNat, writeScalar, next, startupRoot, startup, hn.ne']

theorem startup_invariant {n : ℕ} (x : Fin n → ℂ) : outerInvariant x 0 (startup n) := by
  simp [outerInvariant, context, startup, startupRoot, writeNat, writeScalar, next, initial]

theorem halt_executes {n : ℕ} (x : Fin n → ℂ) (s : State) (hs : outerInvariant x n s) :
    Executes program n x s 2 { s with pc := 20 } := by
  obtain ⟨⟨hn, hk, _, _, _, _⟩, hp, _⟩ := hs
  refine .next (u := { s with pc := 20 }) ?_ (.halt ?_)
  · simp [step, program, hn, hk, hp]
  · simp [step, program]

/-- One literal finite program computes every positive DFT; all preparation and
    loop instructions are charged. The direct fallback has quadratic time. -/
theorem direct_execution {n : ℕ} (hn : 0 < n) (x : Fin n → ℂ) :
    ∃ s, Executes program n x initial (7 * n ^ 2 + 9 * n + 7) s ∧
      ComputesDFT n x s ∧ s.rootOrders = [n] := by
  obtain ⟨s, hr, hi⟩ := outer_loop x n 0 (startup n) (by omega) (startup_invariant x)
  refine ⟨{ s with pc := 20 }, ?_, ?_, hi.1.2.2.2.2.2⟩
  · convert ((startup_runs hn x).trans hr).executes (halt_executes x s hi) using 1; ring
  · intro j
    exact hi.2.2 j j.isLt

theorem direct_root_bound {n : ℕ} (hn : 0 < n) : n < 1024 * n ^ 3 := by
  have h1 : 1 ≤ n := hn
  have h2 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ h1
  rw [pow_succ]
  nlinarith

end
end ExactFourierCircuits.UniformDirectMachine

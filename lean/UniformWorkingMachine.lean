import UniformPrimeMachine

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.1, Lemma 5.1, PDF p.21 (`lem:prime-lengths`).

Literal trial-division selection and accepted-prime table writes implement
the stopping-product argument. Registers, frames and relocation are additional
implementation bookkeeping, without a separate paper lemma.
-/
set_option autoImplicit false

namespace ExactFourierCircuits.UniformWorkingMachine
open UniformMachine
noncomputable section

/- Prime helper workspace0..7; n=8, zero=9, selected count=10,
   selected product=11, two=12, twice n=13, tested product=14, one=15.
   The only table writes are the accepted primes at consecutive addresses0,1,... . -/
/- Paper stage: §5.1, Lemma 5.1, PDF p.21: literal integer selection program. Register allocation and relocation have no direct paper counterpart. -/
def header : Program :=
  [.length 8, .natLiteral 0 3, .natLiteral 10 0, .natLiteral 11 1,
   .natLiteral 12 2, .natBinary .mul 13 8 12, .natLiteral 9 0,
   .natLiteral 15 1, .jump 9]

def suffix : Program :=
  [.branchLT 9 7 25 30, .natBinary .mul 14 11 0, .branchLT 13 14 32 27,
   .storeNat 10 0, .natBinary .add 10 10 15, .natBinary .sub 11 14 9,
   .natBinary .add 0 0 15, .jump 9, .halt]

def program : Program := UniformAssembly.embed header UniformPrimeMachine.program suffix 24

theorem prime_code : UniformAssembly.CodeAt UniformPrimeMachine.program program 9 24 := by
  exact UniformAssembly.embed_code header UniformPrimeMachine.program suffix 24

theorem program_length : program.length = 33 := by decide

/- Paper stage: Implementation bookkeeping for §5.1, Lemma 5.1, PDF p.21: maintained candidate/product state and accepted-prime directory. -/
def Invariant (n p j R : ℕ) (s : State) : Prop :=
  s.pc = 9 ∧ s.natReg 0 = p ∧ s.natReg 8 = n ∧ s.natReg 9 = 0 ∧
    s.natReg 10 = j ∧ s.natReg 11 = R ∧ s.natReg 12 = 2 ∧
    s.natReg 13 = 2 * n ∧ s.natReg 15 = 1

def PrimeTable (j : ℕ) (s : State) : Prop :=
  ∀ i, i < j → s.natHeap i = some (UniformWorkingLength.oddPrime i)

def Frame (s u : State) : Prop :=
  u.scalarReg = s.scalarReg ∧ u.scalarHeap = s.scalarHeap ∧
    u.outputs = s.outputs ∧ u.rootOrders = s.rootOrders ∧
    ∀ r, r = 8 ∨ r = 9 ∨ r = 12 ∨ r = 13 ∨ r = 15 ∨ 16 ≤ r → u.natReg r = s.natReg r

theorem frame_refl (s : State) : Frame s s := ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Frame.trans {s u v : State} (h : Frame s u) (h' : Frame u v) : Frame s v := by
  exact ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.1.trans h.2.2.2.1,
    fun r hr => (h'.2.2.2.2 r hr).trans (h.2.2.2.2 r hr)⟩

theorem prime_frame {s u : State} (h : UniformPrimeMachine.Frame s u) : Frame s u := by
  exact ⟨h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2,
    fun r hr => h.2.1 r (by omega)⟩

theorem helper_bounded (V n : ℕ) (x : Fin n → ℂ) (s : State)
    (hV : 33 ≤ V) (hp : s.pc = 9) (hb : WordBound V s) : ∃ u : State,
    BoundedRuns program n x (V + 9) s (UniformPrimeMachine.totalCost (s.natReg 0)) u ∧
      WordBound V u ∧ u.pc = 24 ∧ (u.natReg 7 = 1 ↔ Nat.Prime (s.natReg 0)) ∧
      (u.natReg 7 = 0 ∨ u.natReg 7 = 1) ∧ UniformPrimeMachine.Frame s u := by
  let entered := { s with pc := 0 }
  have he : WordBound V entered := changePC_bound _ _ 0 hb (by omega)
  obtain ⟨u, hu, hpc, hv, hbool, hf⟩ := UniformPrimeMachine.bounded_prime_correct
    V n x entered (by omega) rfl he
  refine ⟨{ u with pc := 24 }, ?_, changePC_bound _ _ 24 hu.final_bound (by omega),
    rfl, hv, hbool, hf⟩
  have hr := UniformAssembly.BoundedExecution.placed prime_code
    (by omega : 9 + V ≤ V + 9) (by omega : 24 ≤ V + 9) hu
  have heq : UniformAssembly.placed 9 entered = s := by
    cases s
    simp_all [UniformAssembly.placed, entered]
  rw [heq] at hr
  exact hr

def tested (s : State) : State := writeNat { s with pc := 25 } 14 (s.natReg 11 * s.natReg 0)
def stored (s : State) : State :=
  ⟨28, (tested s).natReg, s.scalarReg,
    Function.update s.natHeap (s.natReg 10) (some (s.natReg 0)),
    s.scalarHeap, s.outputs, s.rootOrders⟩
def counted (s : State) : State := writeNat (stored s) 10 (s.natReg 10 + 1)
def multiplied (s : State) : State := writeNat (counted s) 11 (s.natReg 11 * s.natReg 0)
def accepted (s : State) : State :=
  { writeNat (multiplied s) 0 (s.natReg 0 + 1) with pc := 9 }
def skipped (s : State) : State :=
  { writeNat { s with pc := 30 } 0 (s.natReg 0 + 1) with pc := 9 }

theorem accepted_invariant (n p j R : ℕ) (s : State)
    (hs : s.pc = 24 ∧ s.natReg 0 = p ∧ s.natReg 8 = n ∧ s.natReg 9 = 0 ∧
      s.natReg 10 = j ∧ s.natReg 11 = R ∧ s.natReg 12 = 2 ∧
      s.natReg 13 = 2 * n ∧ s.natReg 15 = 1) :
    Invariant n (p + 1) (j + 1) (R * p) (accepted s) := by
  obtain ⟨_, h0, h8, h9, h10, h11, h12, h13, h15⟩ := hs
  simp [Invariant, accepted, multiplied, counted, stored, tested, writeNat, next,
    h0, h8, h9, h10, h11, h12, h13, h15]

theorem skipped_invariant (n p j R : ℕ) (s : State)
    (hs : s.pc = 24 ∧ s.natReg 0 = p ∧ s.natReg 8 = n ∧ s.natReg 9 = 0 ∧
      s.natReg 10 = j ∧ s.natReg 11 = R ∧ s.natReg 12 = 2 ∧
      s.natReg 13 = 2 * n ∧ s.natReg 15 = 1) : Invariant n (p + 1) j R (skipped s) := by
  obtain ⟨_, h0, h8, h9, h10, h11, h12, h13, h15⟩ := hs
  simp [Invariant, skipped, writeNat, next, h0, h8, h9, h10, h11, h12, h13, h15]

theorem body_frames (s : State) : Frame s (accepted s) ∧ Frame s (skipped s) ∧
    Frame s { tested s with pc := 32 } := by
  refine ⟨?_, ?_, ?_⟩
  all_goals refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  all_goals intro r hr
  all_goals have h0 : r ≠ 0 := by omega
  all_goals have h10 : r ≠ 10 := by omega
  all_goals have h11 : r ≠ 11 := by omega
  all_goals have h14 : r ≠ 14 := by omega
  all_goals simp [accepted, multiplied, counted, stored, tested, skipped, writeNat, next,
    h0, h10, h11, h14]

theorem accepted_heap (s : State) : (accepted s).natHeap =
    Function.update s.natHeap (s.natReg 10) (some (s.natReg 0)) := rfl

theorem skipped_heap (s : State) : (skipped s).natHeap = s.natHeap := rfl

theorem tested_heap (s : State) : (tested s).natHeap = s.natHeap := rfl

theorem skip_bounded (V n : ℕ) (x : Fin n → ℂ) (s : State) (hV : 33 ≤ V)
    (hb : WordBound V s) (hp : s.pc = 24) (hz : s.natReg 9 = 0)
    (hone : s.natReg 15 = 1) (hresult : s.natReg 7 = 0) (hnext : s.natReg 0 + 1 ≤ V) :
    BoundedRuns program n x V s 3 (skipped s) := by
  have h30 := changePC_bound V s 30 hb (by omega)
  have h31 := writeNat_bound V { s with pc := 30 } 0 (s.natReg 0 + 1) h30
    (by simp; omega) hnext
  have h9 := changePC_bound V _ 9 h31 (by omega)
  refine .next hb (u := { s with pc := 30 }) ?_
    (.next h30 (u := writeNat { s with pc := 30 } 0 (s.natReg 0 + 1)) ?_
      (.next h31 (u := skipped s) ?_ (.refl h9)))
  all_goals simp [step, program, UniformAssembly.embed, UniformAssembly.relocate,
    header, suffix, UniformPrimeMachine.program, skipped, writeNat, next, evalNat,
    hp, hz, hone, hresult]

theorem test_bounded (V n : ℕ) (x : Fin n → ℂ) (s : State) (hV : 33 ≤ V)
    (hb : WordBound V s) (hp : s.pc = 24) (hz : s.natReg 9 = 0)
    (hresult : s.natReg 7 = 1) (hprod : s.natReg 11 * s.natReg 0 ≤ V) :
    BoundedRuns program n x V s 2 (tested s) := by
  have h25 := changePC_bound V s 25 hb (by omega)
  have h26 := writeNat_bound V { s with pc := 25 } 14 (s.natReg 11 * s.natReg 0) h25
    (by simp; omega) hprod
  refine .next hb (u := { s with pc := 25 }) ?_
    (.next h25 (u := tested s) ?_ (.refl h26))
  all_goals simp [step, program, UniformAssembly.embed, UniformAssembly.relocate,
    header, suffix, UniformPrimeMachine.program, tested, writeNat, next, evalNat,
    hp, hz, hresult]

theorem accept_bounded (V n : ℕ) (x : Fin n → ℂ) (s : State) (hV : 33 ≤ V)
    (hb : WordBound V s) (hp : s.pc = 24) (hz : s.natReg 9 = 0)
    (hone : s.natReg 15 = 1) (hresult : s.natReg 7 = 1)
    (hprod : s.natReg 11 * s.natReg 0 ≤ V)
    (hkeep : ¬s.natReg 13 < s.natReg 11 * s.natReg 0)
    (hnext : s.natReg 0 + 1 ≤ V) (hcount : s.natReg 10 + 1 ≤ V) :
    BoundedRuns program n x V s 8 (accepted s) := by
  have hr := test_bounded V n x s hV hb hp hz hresult hprod
  have h27 := changePC_bound V (tested s) 27 hr.final_bound (by omega)
  have hstore : WordBound V (stored s) := by
    obtain ⟨_, hreg, hn, hscalar, ho, hd⟩ := hb
    refine ⟨by simp [stored]; omega, ?_, ?_, hscalar, ho, hd⟩
    · exact (hr.final_bound).2.1
    · intro a v ha
      by_cases he : a = s.natReg 10
      · subst a
        simp [stored, tested, writeNat, next] at ha
        subst v
        exact ⟨hreg 10, hreg 0⟩
      · exact hn a v (by simpa [stored, tested, writeNat, next, he] using ha)
  have hc := writeNat_bound V (stored s) 10 (s.natReg 10 + 1) hstore
    (by simp [stored]; omega) hcount
  have hm := writeNat_bound V (counted s) 11 (s.natReg 11 * s.natReg 0) hc
    (by simp [counted, stored, writeNat, next]; omega) hprod
  have hi := writeNat_bound V (multiplied s) 0 (s.natReg 0 + 1) hm
    (by simp [multiplied, counted, stored, writeNat, next]; omega) hnext
  have hf := changePC_bound V _ 9 hi (by omega)
  have ht : BoundedRuns program n x V (tested s) 6 (accepted s) := by
    refine .next hr.final_bound (u := { tested s with pc := 27 }) ?_
      (.next h27 (u := stored s) ?_ (.next hstore (u := counted s) ?_
        (.next hc (u := multiplied s) ?_
          (.next hm (u := writeNat (multiplied s) 0 (s.natReg 0 + 1)) ?_
            (.next hi (u := accepted s) ?_ (.refl hf))))))
    all_goals simp [step, program, UniformAssembly.embed, UniformAssembly.relocate,
      header, suffix, UniformPrimeMachine.program, accepted, multiplied, counted,
      stored, tested, writeNat, next, evalNat, hz, hone, hkeep]
  exact hr.trans ht

theorem boundedRuns_mono {p : Program} {n B C t : ℕ} {x : Fin n → ℂ} {s u : State}
    (hBC : B ≤ C) (h : BoundedRuns p n x B s t u) : BoundedRuns p n x C s t u := by
  induction h with
  | refl hb => exact .refl (UniformAssembly.wordBound_mono hBC hb)
  | next hb hs _ ih => exact .next (UniformAssembly.wordBound_mono hBC hb) hs ih

theorem accepted_table (p j : ℕ) (s : State) (hp : s.natReg 0 = p)
    (hj : s.natReg 10 = j) (hprime : p = UniformWorkingLength.oddPrime j)
    (ht : PrimeTable j s) : PrimeTable (j + 1) (accepted s) := by
  intro i hi
  rw [accepted_heap, hj, hp]
  by_cases he : i = j
  · subst i; simp [hprime]
  · simpa [he] using ht i (by omega)

theorem scan_cost_advance (p q call extra tail : ℕ) (hp : p < q)
    (hcall : call ≤ 6 * p + 11) (hextra : extra ≤ 8)
    (htail : tail ≤ (q - (p + 1) + 1) * (6 * q + 19)) :
    call + extra + tail ≤ (q - p + 1) * (6 * q + 19) := by
  have hd : q - p + 1 = (q - (p + 1) + 1) + 1 := by omega
  rw [hd, Nat.add_mul, Nat.one_mul]
  omega

/-- The induction parameter is a proof of termination; it is not read by the machine.
    Every candidate, prime call, product test, table write and jump is executed. -/
theorem scan_bounded (V n : ℕ) (x : Fin n → ℂ) (hn : 0 < n) (fuel p j : ℕ)
    (s : State) (hV : 33 ≤ V) (h3 : 3 ≤ p) (hpq : p ≤ UniformWorkingLength.nextPrime n)
    (hj : j ≤ UniformWorkingLength.axisCount n)
    (hc : Nat.primeCounting' p = j + 1)
    (hf : UniformWorkingLength.nextPrime n - p + 1 ≤ fuel)
    (hqV : UniformWorkingLength.nextPrime n + 1 ≤ V)
    (hprodV : (2 * n) * UniformWorkingLength.nextPrime n ≤ V)
    (hs : Invariant n p j (UniformWorkingLength.primeProduct j) s)
    (hb : WordBound V s) (ht : PrimeTable j s) : ∃ t u,
    BoundedRuns program n x (V + 9) s t u ∧ WordBound V u ∧ u.pc = 32 ∧
      u.natReg 0 = UniformWorkingLength.nextPrime n ∧
      u.natReg 10 = UniformWorkingLength.axisCount n ∧
      u.natReg 11 = UniformWorkingLength.oddProduct n ∧
      PrimeTable (UniformWorkingLength.axisCount n) u ∧
      (∀ i, UniformWorkingLength.axisCount n ≤ i → u.natHeap i = s.natHeap i) ∧
      Frame s u ∧ t ≤ (UniformWorkingLength.nextPrime n - p + 1) *
        (6 * UniformWorkingLength.nextPrime n + 19) := by
  induction fuel generalizing p j s with
  | zero => omega
  | succ fuel ih =>
    obtain ⟨hpc, h0, h8, h9, h10, h11, h12, h13, h15⟩ := hs
    obtain ⟨v, hcall0, hvB, hvpc, hvprime0, hvbool, hvframe⟩ := helper_bounded V n x s hV hpc hb
    have hcall : BoundedRuns program n x (V + 9) s (UniformPrimeMachine.totalCost p) v := by
      simpa [h0] using hcall0
    have hvprime : v.natReg 7 = 1 ↔ Nat.Prime p := by simpa [h0] using hvprime0
    have hv0 : v.natReg 0 = p := hvframe.1.trans h0
    have hvreg (r : ℕ) (hr : 8 ≤ r) : v.natReg r = s.natReg r := hvframe.2.1 r hr
    have hv8 : v.natReg 8 = n := (hvreg 8 (by decide)).trans h8
    have hv9 : v.natReg 9 = 0 := (hvreg 9 (by decide)).trans h9
    have hv10 : v.natReg 10 = j := (hvreg 10 (by decide)).trans h10
    have hv11 : v.natReg 11 = UniformWorkingLength.primeProduct j := (hvreg 11 (by decide)).trans h11
    have hv12 : v.natReg 12 = 2 := (hvreg 12 (by decide)).trans h12
    have hv13 : v.natReg 13 = 2 * n := (hvreg 13 (by decide)).trans h13
    have hv15 : v.natReg 15 = 1 := (hvreg 15 (by decide)).trans h15
    have hvInv : v.pc = 24 ∧ v.natReg 0 = p ∧ v.natReg 8 = n ∧ v.natReg 9 = 0 ∧
        v.natReg 10 = j ∧ v.natReg 11 = UniformWorkingLength.primeProduct j ∧
        v.natReg 12 = 2 ∧ v.natReg 13 = 2 * n ∧ v.natReg 15 = 1 :=
      ⟨hvpc, hv0, hv8, hv9, hv10, hv11, hv12, hv13, hv15⟩
    have hvheap : v.natHeap = s.natHeap := hvframe.2.2.2.1
    have hvt : PrimeTable j v := by simpa [PrimeTable, hvheap] using ht
    have hR : UniformWorkingLength.primeProduct j ≤ 2 * n :=
      (UniformWorkingLength.primeProduct_strictMono.monotone hj).trans
        (UniformWorkingLength.maximal_product hn).1
    have hprod : v.natReg 11 * v.natReg 0 ≤ V := by
      rw [hv11, hv0]
      exact (Nat.mul_le_mul hR hpq).trans hprodV
    have hcost := UniformPrimeMachine.totalCost_bound p
    by_cases he : p = UniformWorkingLength.nextPrime n
    · have hprime : Nat.Prime p := he ▸ UniformWorkingLength.oddPrime_prime _
      have hjend : j = UniformWorkingLength.axisCount n := by
        have hcend := UniformWorkingLength.oddPrime_count (UniformWorkingLength.axisCount n)
        change Nat.primeCounting' (UniformWorkingLength.nextPrime n) = _ at hcend
        rw [he] at hc
        omega
      have hstop : v.natReg 13 < v.natReg 11 * v.natReg 0 := by
        rw [hv13, hv11, hv0, hjend, he]
        exact (UniformWorkingLength.maximal_product hn).2
      have htest := test_bounded V n x v hV hvB hvpc hv9 (hvprime.mpr hprime) hprod
      let u := { tested v with pc := 32 }
      have huB : WordBound V u := changePC_bound _ _ 32 htest.final_bound (by omega)
      have hlast : BoundedRuns program n x V (tested v) 1 u := by
        refine .next htest.final_bound (u := u) ?_ (.refl huB)
        simp [step, program, UniformAssembly.embed, UniformAssembly.relocate,
          header, suffix, UniformPrimeMachine.program, tested, writeNat, next, u, hstop]
      refine ⟨UniformPrimeMachine.totalCost p + 3, u, ?_, huB, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hcall.trans (boundedRuns_mono (by omega) (htest.trans hlast))
      · simpa [u, tested, writeNat] using hv0.trans he
      · simpa [u, tested, writeNat] using hv10.trans hjend
      · simpa [u, tested, writeNat, hjend, UniformWorkingLength.oddProduct] using hv11
      · simpa [PrimeTable, u, tested, writeNat, next, hvheap, ← hjend] using ht
      · intro i _; simp [u, tested, writeNat, next, hvheap]
      · exact (prime_frame hvframe).trans (body_frames v).2.2
      · rw [he]
        simp only [Nat.sub_self, Nat.zero_add, Nat.one_mul]
        have hcost' := UniformPrimeMachine.totalCost_bound (UniformWorkingLength.nextPrime n)
        omega
    · have hlt : p < UniformWorkingLength.nextPrime n := by omega
      have hnext : v.natReg 0 + 1 ≤ V := by omega
      by_cases hprime : Nat.Prime p
      · have hpj := UniformWorkingPreparation.prime_of_count hprime hc
        have hjlt : j < UniformWorkingLength.axisCount n := by
          by_contra h
          have hm := UniformWorkingLength.oddPrime_strictMono.monotone
            (show UniformWorkingLength.axisCount n ≤ j by omega)
          rw [← hpj] at hm
          change UniformWorkingLength.nextPrime n ≤ p at hm
          omega
        have hnew : UniformWorkingLength.primeProduct j * p =
            UniformWorkingLength.primeProduct (j + 1) := by rw [hpj, UniformWorkingLength.primeProduct]
        have hkeep : ¬v.natReg 13 < v.natReg 11 * v.natReg 0 := by
          rw [hv13, hv11, hv0, hnew]
          have hm := (UniformWorkingLength.primeProduct_strictMono.monotone
            (show j + 1 ≤ UniformWorkingLength.axisCount n by omega)).trans
            (UniformWorkingLength.maximal_product hn).1
          omega
        have hjq := UniformWorkingLength.oddPrime_lower (UniformWorkingLength.axisCount n)
        change UniformWorkingLength.axisCount n + 3 ≤ UniformWorkingLength.nextPrime n at hjq
        have hcount : v.natReg 10 + 1 ≤ V := by omega
        have hbody := accept_bounded V n x v hV hvB hvpc hv9 hv15 (hvprime.mpr hprime)
          hprod hkeep hnext hcount
        have hInv : Invariant n (p + 1) (j + 1) (UniformWorkingLength.primeProduct (j + 1)) (accepted v) := by
          rw [← hnew]
          exact accepted_invariant n p j (UniformWorkingLength.primeProduct j) v hvInv
        have htab := accepted_table p j v hv0 hv10 hpj hvt
        have hc' : Nat.primeCounting' (p + 1) = (j + 1) + 1 := by
          simp only [UniformWorkingPreparation.counting_succ, hprime, ite_true, hc]
        obtain ⟨t, u, hr, huB, huPC, hu0, hu10, hu11, hut, hheap, hframe, htbound⟩ :=
          ih (p + 1) (j + 1) (accepted v) (by omega) (by omega) (by omega) hc'
            (by omega) hInv hbody.final_bound htab
        refine ⟨UniformPrimeMachine.totalCost p + 8 + t, u, ?_, huB, huPC, hu0, hu10,
          hu11, hut, ?_, ?_, ?_⟩
        · exact (hcall.trans (boundedRuns_mono (by omega) hbody)).trans hr
        · intro i hi
          rw [hheap i hi, accepted_heap, hv10, hvheap]
          simp [show i ≠ j by omega]
        · exact (prime_frame hvframe).trans ((body_frames v).1.trans hframe)
        · exact scan_cost_advance p _ _ 8 t hlt hcost (by decide) htbound
      · have hzero : v.natReg 7 = 0 := by
          rcases hvbool with hz | hone
          · exact hz
          · exact (hprime (hvprime.mp hone)).elim
        have hbody := skip_bounded V n x v hV hvB hvpc hv9 hv15 hzero hnext
        have hc' : Nat.primeCounting' (p + 1) = j + 1 := by
          simp only [UniformWorkingPreparation.counting_succ, hprime, ite_false, hc, Nat.add_zero]
        have htab : PrimeTable j (skipped v) := by simpa [PrimeTable, skipped_heap] using hvt
        obtain ⟨t, u, hr, huB, huPC, hu0, hu10, hu11, hut, hheap, hframe, htbound⟩ :=
          ih (p + 1) j (skipped v) (by omega) (by omega) hj hc' (by omega)
            (skipped_invariant n p j (UniformWorkingLength.primeProduct j) v hvInv)
            hbody.final_bound htab
        refine ⟨UniformPrimeMachine.totalCost p + 3 + t, u, ?_, huB, huPC, hu0, hu10,
          hu11, hut, ?_, ?_, ?_⟩
        · exact (hcall.trans (boundedRuns_mono (by omega) hbody)).trans hr
        · intro i hi
          rw [hheap i hi, skipped_heap, hvheap]
        · exact (prime_frame hvframe).trans ((body_frames v).2.1.trans hframe)
        · exact scan_cost_advance p _ _ 3 t hlt hcost (by decide) htbound

def started (n : ℕ) : State :=
  { writeNat (writeNat (writeNat (writeNat (writeNat
      (writeNat (writeNat (writeNat initial 8 n) 0 3) 10 0) 11 1) 12 2)
      13 (2 * n)) 9 0) 15 1 with pc := 9 }

theorem start_bounded (V n : ℕ) (x : Fin n → ℂ) (hV : 33 ≤ V)
    (hn : n ≤ V) (htwon : 2 * n ≤ V) : BoundedRuns program n x V initial 9 (started n) := by
  have h0 := initial_wordBound V
  have h1 := writeNat_bound V initial 8 n h0 (by simp [initial]; omega) hn
  have h2 := writeNat_bound V (writeNat initial 8 n) 0 3 h1
    (by simp [writeNat, next, initial]; omega) (by omega)
  have h3 := writeNat_bound V (writeNat (writeNat initial 8 n) 0 3) 10 0 h2
    (by simp [writeNat, next, initial]; omega) (by omega)
  have h4 := writeNat_bound V (writeNat (writeNat (writeNat initial 8 n) 0 3) 10 0) 11 1 h3
    (by simp [writeNat, next, initial]; omega) (by omega)
  have h5 := writeNat_bound V (writeNat (writeNat (writeNat (writeNat initial 8 n) 0 3) 10 0) 11 1)
    12 2 h4 (by simp [writeNat, next, initial]; omega) (by omega)
  have h6 := writeNat_bound V (writeNat (writeNat (writeNat (writeNat (writeNat initial 8 n) 0 3)
    10 0) 11 1) 12 2) 13 (2 * n) h5 (by simp [writeNat, next, initial]; omega) htwon
  have h7 := writeNat_bound V (writeNat (writeNat (writeNat (writeNat (writeNat
    (writeNat initial 8 n) 0 3) 10 0) 11 1) 12 2) 13 (2 * n)) 9 0 h6
    (by simp [writeNat, next, initial]; omega) (by omega)
  have h8 := writeNat_bound V (writeNat (writeNat (writeNat (writeNat (writeNat
    (writeNat (writeNat initial 8 n) 0 3) 10 0) 11 1) 12 2) 13 (2 * n)) 9 0) 15 1 h7
    (by simp [writeNat, next, initial]; omega) (by omega)
  have h9 := changePC_bound V _ 9 h8 (by omega)
  refine .next h0 (u := writeNat initial 8 n) ?_
    (.next h1 (u := writeNat (writeNat initial 8 n) 0 3) ?_
      (.next h2 (u := writeNat (writeNat (writeNat initial 8 n) 0 3) 10 0) ?_
        (.next h3 (u := writeNat (writeNat (writeNat (writeNat initial 8 n) 0 3) 10 0) 11 1) ?_
          (.next h4 (u := writeNat (writeNat (writeNat (writeNat (writeNat initial 8 n) 0 3) 10 0) 11 1) 12 2) ?_
            (.next h5 (u := writeNat (writeNat (writeNat (writeNat (writeNat
              (writeNat initial 8 n) 0 3) 10 0) 11 1) 12 2) 13 (2 * n)) ?_
              (.next h6 (u := writeNat (writeNat (writeNat (writeNat (writeNat
                (writeNat (writeNat initial 8 n) 0 3) 10 0) 11 1) 12 2) 13 (2 * n)) 9 0) ?_
                (.next h7 (u := writeNat (writeNat (writeNat (writeNat (writeNat
                  (writeNat (writeNat (writeNat initial 8 n) 0 3) 10 0) 11 1) 12 2) 13 (2 * n)) 9 0) 15 1) ?_
                  (.next h8 (u := started n) ?_ (.refl h9)))))))))
  all_goals simp [step, program, UniformAssembly.embed, UniformAssembly.relocate,
    header, suffix, UniformPrimeMachine.program, started, writeNat, next, evalNat, initial, Nat.mul_comm]

theorem started_invariant (n : ℕ) : Invariant n 3 0 1 (started n) := by
  simp [Invariant, started, writeNat, next, initial]

theorem started_heap (n : ℕ) : (started n).natHeap = initial.natHeap := rfl

/-- Bounds the tested stopping product as well as every candidate and stored prime. -/
def wordBound (n : ℕ) : ℕ := (2 * n + 1) * (UniformWorkingLength.nextPrime n + 1) + 40

theorem wordBound_ge (n : ℕ) : 33 ≤ wordBound n ∧ n ≤ wordBound n ∧
    2 * n ≤ wordBound n ∧ UniformWorkingLength.nextPrime n + 1 ≤ wordBound n ∧
    (2 * n) * UniformWorkingLength.nextPrime n ≤ wordBound n := by
  have hq : 0 < UniformWorkingLength.nextPrime n := (UniformWorkingLength.oddPrime_prime _).pos
  dsimp [wordBound]
  constructor
  · omega
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The prefix-only fixed program, started by the actual length instruction.
    Its initialized Nat heap contains exactly the selected initial odd-prime table. -/
/- Paper stage: §5.1, Lemma 5.1, PDF p.21: actual empty-state execution supplies the selected product and prime table, rather than executing Nat.find. -/
theorem prefix_execution {n : ℕ} (hn : 0 < n) (x : Fin n → ℂ) : ∃ t u,
    BoundedExecution program n x (wordBound n + 9) initial t u ∧ u.pc = 32 ∧
      u.natReg 8 = n ∧ u.natReg 0 = UniformWorkingLength.nextPrime n ∧
      u.natReg 10 = UniformWorkingLength.axisCount n ∧
      u.natReg 11 = UniformWorkingLength.oddProduct n ∧
      PrimeTable (UniformWorkingLength.axisCount n) u ∧
      (∀ i, UniformWorkingLength.axisCount n ≤ i → u.natHeap i = none) ∧
      u.scalarReg = initial.scalarReg ∧ u.scalarHeap = initial.scalarHeap ∧
      u.outputs = initial.outputs ∧ u.rootOrders = [] ∧
      t ≤ UniformWorkingLength.nextPrime n * (6 * UniformWorkingLength.nextPrime n + 19) + 10 := by
  obtain ⟨hV, hnV, h2nV, hqV, hprodV⟩ := wordBound_ge n
  have hstart := start_bounded (wordBound n) n x hV hnV h2nV
  have hq3 : 3 ≤ UniformWorkingLength.nextPrime n := by
    have h := UniformWorkingLength.oddPrime_lower (UniformWorkingLength.axisCount n)
    change UniformWorkingLength.axisCount n + 3 ≤ UniformWorkingLength.nextPrime n at h
    omega
  obtain ⟨t, u, hr, huB, hp, h0, h10, h11, htab, hheap, hframe, hcost⟩ :=
    scan_bounded (wordBound n) n x hn (UniformWorkingLength.nextPrime n) 3 0 (started n)
      hV (by decide) hq3 (by omega) (by norm_num [Nat.primeCounting', Nat.count_succ])
      (by omega) hqV hprodV (started_invariant n) hstart.final_bound (by simp [PrimeTable])
  have hhalt : BoundedExecution program n x (wordBound n + 9) u 1 u := by
    refine .halt (UniformAssembly.wordBound_mono (by omega) huB) ?_
    simp [step, program, UniformAssembly.embed, UniformAssembly.relocate,
      header, suffix, UniformPrimeMachine.program, hp]
  refine ⟨9 + t + 1, u, ?_, hp, ?_, h0, h10, h11, htab, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((boundedRuns_mono (by omega) hstart).trans hr).executes hhalt
  · have h8 := hframe.2.2.2.2 8 (by simp)
    simpa [started, writeNat, next, initial] using h8
  · intro i hi
    simpa [started_heap, initial] using hheap i hi
  · exact hframe.1
  · exact hframe.2.1
  · exact hframe.2.2.1
  · exact hframe.2.2.2.1
  · have hm := Nat.mul_le_mul_right (6 * UniformWorkingLength.nextPrime n + 19)
      (show UniformWorkingLength.nextPrime n - 3 + 1 ≤ UniformWorkingLength.nextPrime n by omega)
    omega

theorem prefix_cost_polynomial {n : ℕ} (_hn : 0 < n) :
    UniformWorkingLength.nextPrime n * (6 * UniformWorkingLength.nextPrime n + 19) + 10 ≤
      30000 * (UniformWorkingLength.axisCount n + 2) ^ 4 := by
  have hq := UniformWorkingLength.nextPrime_upper n
  have hpow := Nat.pow_le_pow_left hq 2
  have ha : 4 ≤ (UniformWorkingLength.axisCount n + 2) ^ 2 :=
    Nat.pow_le_pow_left (show 2 ≤ UniformWorkingLength.axisCount n + 2 by omega) 2
  have h : UniformWorkingLength.nextPrime n * (6 * UniformWorkingLength.nextPrime n + 19) + 10 ≤
      30000 * ((UniformWorkingLength.axisCount n + 2) ^ 2) ^ 2 := by nlinarith
  simpa only [← pow_mul, Nat.reduceMul] using h

theorem wordBound_polynomial {n : ℕ} (hn : 0 < n) : wordBound n + 9 ≤ (n + 2) ^ 9 := by
  have hj : UniformWorkingLength.axisCount n ≤ 2 * n := by
    have h := UniformWorkingLength.firstExceed_bound n
    unfold UniformWorkingLength.axisCount
    omega
  have hq : UniformWorkingLength.nextPrime n ≤ 64 * (2 * n + 2) ^ 2 :=
    (UniformWorkingLength.nextPrime_upper n).trans
      (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left (Nat.add_le_add_right hj 2) 2))
  have hm := Nat.mul_le_mul_left (2 * n + 1) (Nat.add_le_add_right hq 1)
  have hx : (2 * n + 1) * (64 * (2 * n + 2) ^ 2 + 1) + 49 ≤ 600 * (n + 2) ^ 3 := by
    nlinarith
  have hsmall : wordBound n + 9 ≤ 600 * (n + 2) ^ 3 := by
    dsimp [wordBound]
    omega
  have h600 : 600 ≤ (n + 2) ^ 6 := by
    have h := Nat.pow_le_pow_left (show 3 ≤ n + 2 by omega) 6
    norm_num at h
    omega
  calc
    wordBound n + 9 ≤ 600 * (n + 2) ^ 3 := hsmall
    _ ≤ (n + 2) ^ 6 * (n + 2) ^ 3 := Nat.mul_le_mul_right _ h600
    _ = (n + 2) ^ 9 := by rw [← pow_add]

theorem boundedExecution_mono {p : Program} {n B C t : ℕ} {x : Fin n → ℂ} {s u : State}
    (hBC : B ≤ C) (h : BoundedExecution p n x B s t u) : BoundedExecution p n x C s t u := by
  induction h with
  | halt hb hs => exact .halt (UniformAssembly.wordBound_mono hBC hb) hs
  | next hb hs _ ih => exact .next (UniformAssembly.wordBound_mono hBC hb) hs ih

def SelectedState (n : ℕ) (u : State) : Prop :=
  u.natReg 0 = UniformWorkingLength.nextPrime n ∧
    u.natReg 10 = UniformWorkingLength.axisCount n ∧
    u.natReg 11 = UniformWorkingLength.oddProduct n ∧ PrimeTable (UniformWorkingLength.axisCount n) u ∧
    ∀ i, UniformWorkingLength.axisCount n ≤ i → u.natHeap i = none

/-- Polynomial preparation count and word bounds for an actual fixed prefix program.
    Binary doubling and the enclosing all-length Fourier compiler are separate phases. -/
theorem prefix_polynomial {n : ℕ} (hn : 0 < n) (x : Fin n → ℂ) : ∃ t u,
    BoundedExecution program n x ((n + 2) ^ 9) initial t u ∧ SelectedState n u ∧
      u.pc = 32 ∧ u.natReg 8 = n ∧
      u.scalarReg = initial.scalarReg ∧ u.scalarHeap = initial.scalarHeap ∧
      u.outputs = initial.outputs ∧ u.rootOrders = [] ∧
      t ≤ 30000 * (UniformWorkingLength.axisCount n + 2) ^ 4 := by
  obtain ⟨t, u, hu, hp, h8, h0, h10, h11, htab, hheap, hs, hh, ho, hd, hc⟩ :=
    prefix_execution hn x
  exact ⟨t, u, boundedExecution_mono (wordBound_polynomial hn) hu,
    ⟨h0, h10, h11, htab, hheap⟩, hp, h8, hs, hh, ho, hd, hc.trans (prefix_cost_polynomial hn)⟩

end
end ExactFourierCircuits.UniformWorkingMachine

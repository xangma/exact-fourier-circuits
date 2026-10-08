import UniformBatching
import UniformMachineRuns
import UniformReciprocalMachine

set_option autoImplicit false

namespace ExactFourierCircuits.UniformRecursiveBatchHeaderMachine
open UniformMachine
noncomputable section

/- A fixed charged dispatch for the recursive simultaneous transform. Only
   register 2440 supplies k. The base path does not load the giant fixed
   residual count. The recursive path computes its quotient, batch volume and
   child count by actual integer instructions, including all doublings.
   This dispatch does not execute a child transform. -/
def program : Program :=
  [.natLiteral 2447 UniformBatching.threshold,
   .natLiteral 2446 0,
   .branchLT 2440 2447 20 3,
   .natLiteral 2448 UniformBatching.blockSize,
   .natLiteral 2449 UniformBatching.roleBits,
   .natLiteral 2450 ExplicitSeedBudget.residuals,
   .natLiteral 2451 1,
   .natLiteral 2452 2,
   .natBinary .div 2441 2440 2448,
   .natBinary .sub 2442 2440 2441,
   .natBinary .sub 2442 2442 2449,
   .natLiteral 2443 1,
   .natLiteral 2444 0,
   .branchLT 2444 2442 14 17,
   .natBinary .mul 2443 2443 2452,
   .natBinary .add 2444 2444 2451,
   .jump 13,
   .natBinary .mul 2445 2450 2443,
   .natLiteral 2446 1,
   .jump 24,
   .natLiteral 2441 0,
   .natLiteral 2442 0,
   .natLiteral 2443 0,
   .natLiteral 2445 0,
   .halt]

theorem program_length : program.length = 25 := rfl

def setPC (s : State) (pc : ℕ) : State := {s with pc := pc}
def boot (s : State) : State :=
  writeNat (writeNat s 2447 UniformBatching.threshold) 2446 0
def baseFinal (s : State) : State :=
  writeNat (writeNat (writeNat (writeNat (setPC s 20) 2441 0) 2442 0) 2443 0) 2445 0
def recursiveStart (s : State) : State :=
  let u := writeNat (writeNat (writeNat (writeNat (writeNat (setPC s 3)
    2448 UniformBatching.blockSize) 2449 UniformBatching.roleBits)
    2450 ExplicitSeedBudget.residuals) 2451 1) 2452 2
  let u := writeNat u 2441 (u.natReg 2440 / u.natReg 2448)
  let u := writeNat u 2442 (u.natReg 2440 - u.natReg 2441)
  let u := writeNat u 2442 (u.natReg 2442 - u.natReg 2449)
  writeNat (writeNat u 2443 1) 2444 0

def round (s : State) : State :=
  setPC (writeNat (writeNat (setPC s 14) 2443
    (s.natReg 2443 * s.natReg 2452)) 2444
    (s.natReg 2444 + s.natReg 2451)) 13
def finish (s : State) : State :=
  setPC (writeNat (writeNat (setPC s 17) 2445
    (s.natReg 2450 * s.natReg 2443)) 2446 1) 24

def Loop (k i : ℕ) (s : State) : Prop :=
  s.pc = 13 ∧ s.natReg 2440 = k ∧
  s.natReg 2441 = UniformBatching.quotient k ∧
  s.natReg 2442 = k - UniformBatching.quotient k - UniformBatching.roleBits ∧
  s.natReg 2443 = 2 ^ i ∧ s.natReg 2444 = i ∧
  s.natReg 2450 = ExplicitSeedBudget.residuals ∧
  s.natReg 2451 = 1 ∧ s.natReg 2452 = 2

theorem boot_runs (n : ℕ) (x : Fin n → ℂ) (s : State) (hp : s.pc = 0) :
    Runs program n x s 2 (boot s) := by
  refine .next (u := writeNat s 2447 UniformBatching.threshold) ?_
    (.next (u := boot s) ?_ (.refl _))
  all_goals simp [step, program, boot, hp, writeNat, next]

theorem boot_pc (s : State) (hp : s.pc = 0) : (boot s).pc = 2 := by
  simp [boot, writeNat, next, hp]

theorem base_execution (n : ℕ) (x : Fin n → ℂ) (s : State)
    (hp : s.pc = 2) (ht : s.natReg 2447 = UniformBatching.threshold)
    (hk : s.natReg 2440 < UniformBatching.threshold) :
    Executes program n x s 6 (baseFinal s) := by
  refine .next (u := setPC s 20) ?_
    (.next (u := writeNat (setPC s 20) 2441 0) ?_
    (.next (u := writeNat (writeNat (setPC s 20) 2441 0) 2442 0) ?_
    (.next (u := writeNat (writeNat (writeNat (setPC s 20) 2441 0) 2442 0) 2443 0) ?_
    (.next (u := baseFinal s) ?_ (.halt ?_)))))
  all_goals simp [step, program, baseFinal, setPC, writeNat, next, hp, ht, hk]

theorem base_from_entry (n : ℕ) (x : Fin n → ℂ) (s : State)
    (hp : s.pc = 0) (hk : s.natReg 2440 < UniformBatching.threshold) :
    Executes program n x s 8 (baseFinal (boot s)) := by
  exact (boot_runs n x s hp).executes (base_execution n x (boot s) (boot_pc s hp)
    (by simp [boot, writeNat, next]) (by simpa [boot, writeNat, next] using hk))

theorem recursive_loop (s : State) (k : ℕ) (hk : s.natReg 2440 = k) :
    Loop k 0 (recursiveStart s) := by
  simp [Loop, recursiveStart, setPC, writeNat, next, UniformBatching.quotient, hk]

theorem recursive_start_runs (n : ℕ) (x : Fin n → ℂ) (s : State)
    (hp : s.pc = 2) (ht : s.natReg 2447 = UniformBatching.threshold)
    (hk : UniformBatching.threshold ≤ s.natReg 2440) :
    Runs program n x s 11 (recursiveStart s) := by
  let a := writeNat (setPC s 3) 2448 UniformBatching.blockSize
  let b := writeNat a 2449 UniformBatching.roleBits
  let c := writeNat b 2450 ExplicitSeedBudget.residuals
  let d := writeNat c 2451 1
  let e := writeNat d 2452 2
  let f := writeNat e 2441 (e.natReg 2440 / e.natReg 2448)
  let g := writeNat f 2442 (f.natReg 2440 - f.natReg 2441)
  let h := writeNat g 2442 (g.natReg 2442 - g.natReg 2449)
  let j := writeNat h 2443 1
  refine .next (u := setPC s 3) ?_
    (.next (u := a) ?_ (.next (u := b) ?_ (.next (u := c) ?_
    (.next (u := d) ?_ (.next (u := e) ?_ (.next (u := f) ?_
    (.next (u := g) ?_ (.next (u := h) ?_ (.next (u := j) ?_
    (.next (u := recursiveStart s) ?_ (.refl _)))))))))))
  all_goals simp [step, program, recursiveStart, a, b, c, d, e, f, g, h, j,
    setPC, writeNat, next, evalNat, hp, ht, Nat.not_lt.mpr hk,
    Nat.ne_of_gt UniformBatching.blockSize_pos]

theorem round_loop (s : State) (k i : ℕ) (h : Loop k i s) :
    Loop k (i + 1) (round s) := by
  rcases h with ⟨hp,hk,hq,he,hv,hi,hr,h1,h2⟩
  simp [Loop, round, setPC, writeNat, next, hk, hq, he, hv, hi, hr, h1, h2, pow_succ]

theorem round_runs (n : ℕ) (x : Fin n → ℂ) (s : State) (k i : ℕ)
    (h : Loop k i s) (hi : i < k - UniformBatching.quotient k - UniformBatching.roleBits) :
    Runs program n x s 4 (round s) := by
  rcases h with ⟨hp,hk,hq,he,hv,hit,hr,h1,h2⟩
  refine .next (u := setPC s 14) ?_
    (.next (u := writeNat (setPC s 14) 2443 (s.natReg 2443 * s.natReg 2452)) ?_
    (.next (u := writeNat (writeNat (setPC s 14) 2443
      (s.natReg 2443 * s.natReg 2452)) 2444 (s.natReg 2444 + s.natReg 2451)) ?_
    (.next (u := round s) ?_ (.refl _))))
  all_goals simp [step, program, round, setPC, writeNat, next, evalNat, hp, hit, he, hi]

theorem loop_halt (n : ℕ) (x : Fin n → ℂ) (s : State) (k e : ℕ)
    (h : Loop k e s) (he : e = k - UniformBatching.quotient k - UniformBatching.roleBits) :
    Executes program n x s 5 (finish s) := by
  rcases h with ⟨hp,hk,hq,het,hv,hi,hr,h1,h2⟩
  refine .next (u := setPC s 17) ?_
    (.next (u := writeNat (setPC s 17) 2445 (s.natReg 2450 * s.natReg 2443)) ?_
    (.next (u := writeNat (writeNat (setPC s 17) 2445
      (s.natReg 2450 * s.natReg 2443)) 2446 1) ?_
    (.next (u := finish s) ?_ (.halt ?_))))
  all_goals simp [step, program, finish, setPC, writeNat, next, evalNat, hp, hi, het, he]

def rounds : ℕ → State → State
  | 0, s => s
  | a + 1, s => rounds a (round s)

theorem rounds_loop (a : ℕ) (s : State) (k i : ℕ) (h : Loop k i s) :
    Loop k (i + a) (rounds a s) := by
  induction a generalizing s i with
  | zero => simpa [rounds] using h
  | succ a ih =>
    simpa only [rounds, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (round s) (i + 1) (round_loop s k i h)

theorem rounds_runs (a : ℕ) (n : ℕ) (x : Fin n → ℂ) (s : State) (k i : ℕ)
    (h : Loop k i s) (hi : i + a ≤ k - UniformBatching.quotient k - UniformBatching.roleBits) :
    Runs program n x s (4 * a) (rounds a s) := by
  induction a generalizing s i with
  | zero => exact .refl s
  | succ a ih =>
    have hl : i < k - UniformBatching.quotient k - UniformBatching.roleBits := by omega
    have hr := round_runs n x s k i h hl
    have ht := ih (round s) (i + 1) (round_loop s k i h) (by omega)
    simpa only [rounds, Nat.mul_succ, Nat.add_comm] using hr.trans ht

def recursiveFinal (s : State) : State :=
  let u := recursiveStart (boot s)
  finish (rounds (s.natReg 2440 - UniformBatching.quotient (s.natReg 2440) -
    UniformBatching.roleBits) u)

theorem recursive_execution (n : ℕ) (x : Fin n → ℂ) (s : State)
    (hp : s.pc = 0) (hk : UniformBatching.threshold ≤ s.natReg 2440) :
    Executes program n x s
      (4 * (s.natReg 2440 - UniformBatching.quotient (s.natReg 2440) -
        UniformBatching.roleBits) + 18) (recursiveFinal s) := by
  let k := s.natReg 2440
  let e := k - UniformBatching.quotient k - UniformBatching.roleBits
  have hb := boot_runs n x s hp
  have hp' := recursive_start_runs n x (boot s) (boot_pc s hp)
    (by simp [boot, writeNat, next]) (by simpa [boot, writeNat, next] using hk)
  have hl := recursive_loop (boot s) k (by simp [boot, writeNat, next, k])
  have hrounds := rounds_runs e n x (recursiveStart (boot s)) k 0 hl (by simp [e])
  have hloop := rounds_loop e (recursiveStart (boot s)) k 0 hl
  have hend := loop_halt n x _ k e (by simpa using hloop) rfl
  have execution := (hb.trans hp').executes (hrounds.executes hend)
  have ht : (2 + 11) + (4 * e + 5) = 4 * e + 18 := by omega
  rw [ht] at execution
  exact execution

theorem recursive_result (s : State) :
    (recursiveFinal s).natReg 2441 = UniformBatching.quotient (s.natReg 2440) ∧
    (recursiveFinal s).natReg 2443 = UniformBatching.batchCount (s.natReg 2440) ∧
    (recursiveFinal s).natReg 2445 = ExplicitSeedBudget.residuals *
      UniformBatching.batchCount (s.natReg 2440) ∧
    (recursiveFinal s).natReg 2446 = 1 := by
  have h := rounds_loop (s.natReg 2440 - UniformBatching.quotient (s.natReg 2440) -
      UniformBatching.roleBits) (recursiveStart (boot s)) (s.natReg 2440) 0
      (recursive_loop (boot s) _ (by simp [boot, writeNat, next]))
  rcases h with ⟨hp,hk,hq,he,hv,hi,hr,h1,h2⟩
  simp only [Nat.zero_add] at hv
  simp [recursiveFinal, finish, setPC, writeNat, next, hq, hv, hr, UniformBatching.batchCount]

/-- Dispatch changes no data, heap, output, root request or unrelated header. -/
structure Frame (s t : State) : Prop where
  natHeap : t.natHeap = s.natHeap
  scalarHeap : t.scalarHeap = s.scalarHeap
  scalarReg : t.scalarReg = s.scalarReg
  outputs : t.outputs = s.outputs
  roots : t.rootOrders = s.rootOrders
  natReg : ∀ r, r < 2441 ∨ 2452 < r → t.natReg r = s.natReg r

theorem Frame.refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,rfl,rfl,by intros; rfl⟩
theorem Frame.trans {s t u : State} (h : Frame s t) (h' : Frame t u) : Frame s u :=
  ⟨h'.natHeap.trans h.natHeap,h'.scalarHeap.trans h.scalarHeap,
    h'.scalarReg.trans h.scalarReg,h'.outputs.trans h.outputs,
    h'.roots.trans h.roots,by intro r hr; exact (h'.natReg r hr).trans (h.natReg r hr)⟩

theorem frame_pc (s : State) (pc : ℕ) : Frame s (setPC s pc) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,by intros; rfl⟩

theorem frame_write (s : State) (r v : ℕ) (hr : 2441 ≤ r ∧ r ≤ 2452) :
    Frame s (writeNat s r v) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro j hj
  have hn : j ≠ r := by omega
  simp [writeNat, next, hn]

theorem frame_boot (s : State) : Frame s (boot s) :=
  (frame_write s 2447 _ (by omega)).trans (frame_write _ 2446 _ (by omega))

theorem frame_base (s : State) : Frame s (baseFinal s) :=
  (frame_pc s 20).trans ((frame_write _ 2441 _ (by omega)).trans
    ((frame_write _ 2442 _ (by omega)).trans ((frame_write _ 2443 _ (by omega)).trans
    (frame_write _ 2445 _ (by omega)))))

theorem frame_recursive_start (s : State) : Frame s (recursiveStart s) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro r hr
  simp (disch := omega) [recursiveStart, setPC, writeNat, next]

theorem frame_round (s : State) : Frame s (round s) := by
  exact ((frame_pc s 14).trans ((frame_write _ 2443 _ (by omega)).trans
    (frame_write _ 2444 _ (by omega)))).trans (frame_pc _ 13)

theorem frame_finish (s : State) : Frame s (finish s) := by
  exact ((frame_pc s 17).trans ((frame_write _ 2445 _ (by omega)).trans
    (frame_write _ 2446 _ (by omega)))).trans (frame_pc _ 24)

theorem frame_rounds (a : ℕ) (s : State) : Frame s (rounds a s) := by
  induction a generalizing s with
  | zero => exact Frame.refl s
  | succ a ih => exact (frame_round s).trans (ih (round s))

theorem frame_recursive_final (s : State) : Frame s (recursiveFinal s) :=
  (frame_boot s).trans ((frame_recursive_start _).trans
    ((frame_rounds _ _).trans (frame_finish _)))

open UniformReciprocalMachine (Op applyBlock BlockAt block_runs readable peak)

def bootOps : List Op := [.literal 2447 UniformBatching.threshold,.literal 2446 0]
def baseOps : List Op := [.literal 2441 0,.literal 2442 0,.literal 2443 0,.literal 2445 0]
def prepareOps : List Op := [.literal 2448 UniformBatching.blockSize,
  .literal 2449 UniformBatching.roleBits,.literal 2450 ExplicitSeedBudget.residuals,
  .literal 2451 1,.literal 2452 2]
def afterDivideOps : List Op := [.sub 2442 2440 2441,.sub 2442 2442 2449,
  .literal 2443 1,.literal 2444 0]
def roundOps : List Op := [.mul 2443 2443 2452,.add 2444 2444 2451]
def finishOps : List Op := [.mul 2445 2450 2443,.literal 2446 1]

theorem boot_code : BlockAt bootOps program 0 := by
  intro i hi; change i < 2 at hi; interval_cases i <;> rfl
theorem base_code : BlockAt baseOps program 20 := by
  intro i hi; change i < 4 at hi; interval_cases i <;> rfl
theorem prepare_code : BlockAt prepareOps program 3 := by
  intro i hi; change i < 5 at hi; interval_cases i <;> rfl
theorem after_divide_code : BlockAt afterDivideOps program 9 := by
  intro i hi; change i < 4 at hi; interval_cases i <;> rfl
theorem round_code : BlockAt roundOps program 14 := by
  intro i hi; change i < 2 at hi; interval_cases i <;> rfl
theorem finish_code : BlockAt finishOps program 17 := by
  intro i hi; change i < 2 at hi; interval_cases i <;> rfl

theorem pc_bound (s : State) (pc B : ℕ) (hs : WordBound B s) (hp : pc ≤ B) :
    WordBound B (setPC s pc) := ⟨hp,hs.2⟩

theorem boot_bounded (n B : ℕ) (x : Fin n → ℂ) (s : State)
    (hp : s.pc = 0) (hs : WordBound B s) (hc : 24 ≤ B)
    (ht : UniformBatching.threshold ≤ B) :
    BoundedRuns program n x B s 2 (boot s) := by
  have h := block_runs bootOps program 0 n B x s boot_code hp hs (by simp [bootOps]; omega)
    (by simp [readable, bootOps, Op.readable]) (by simpa [peak,bootOps,Op.peak] using ht)
  simpa [bootOps, applyBlock, Op.apply, boot] using h

theorem base_bounded (n B : ℕ) (x : Fin n → ℂ) (s : State)
    (hp : s.pc = 2) (ht : s.natReg 2447 = UniformBatching.threshold)
    (hk : s.natReg 2440 < UniformBatching.threshold)
    (hs : WordBound B s) (hc : 24 ≤ B) :
    BoundedExecution program n x B s 6 (baseFinal s) := by
  have hu := pc_bound s 20 B hs (by omega)
  have h := block_runs baseOps program 20 n B x (setPC s 20) base_code rfl hu
    (by simp [baseOps]; omega) (by simp [readable,baseOps,Op.readable])
    (by simp [peak,baseOps,Op.peak])
  have halt : BoundedExecution program n x B (applyBlock baseOps (setPC s 20)) 1
      (applyBlock baseOps (setPC s 20)) := by
    refine .halt h.final_bound ?_
    simp [step,program,baseOps,applyBlock,Op.apply,setPC,writeNat,next]
  apply BoundedExecution.next hs (u := setPC s 20)
  · simp [step,program,hp,ht,hk,setPC]
  · simpa [baseOps,applyBlock,Op.apply,baseFinal] using h.executes halt

theorem base_bounded_from_entry (n B : ℕ) (x : Fin n → ℂ) (s : State)
    (hp : s.pc = 0) (hk : s.natReg 2440 < UniformBatching.threshold)
    (hs : WordBound B s) (hc : 24 ≤ B) (ht : UniformBatching.threshold ≤ B) :
    BoundedExecution program n x B s 8 (baseFinal (boot s)) := by
  have hb := boot_bounded n B x s hp hs hc ht
  exact hb.executes (base_bounded n B x (boot s) (boot_pc s hp)
    (by simp [boot,writeNat,next]) (by simpa [boot,writeNat,next] using hk) hb.final_bound hc)

/-- Ordinary ambient bounds, computed from k rather than supplied per-step
   safety or a recursive execution certificate. -/
def Budget (k B : ℕ) : Prop :=
  24 ≤ B ∧ UniformBatching.threshold ≤ B ∧ k ≤ B ∧
  ExplicitSeedBudget.residuals ≤ B ∧
  2 ^ (k - UniformBatching.quotient k - UniformBatching.roleBits) ≤ B ∧
  ExplicitSeedBudget.residuals *
    2 ^ (k - UniformBatching.quotient k - UniformBatching.roleBits) ≤ B

theorem constants_le_threshold :
    UniformBatching.blockSize ≤ UniformBatching.threshold ∧
    UniformBatching.roleBits ≤ UniformBatching.threshold := by
  norm_num [UniformBatching.threshold,UniformBatching.blockSize,UniformBatching.roleBits,
    ExplicitSeedBudget.m,ExplicitSeedBudget.roleBits]

theorem recursive_start_bounded (n B : ℕ) (x : Fin n → ℂ) (s : State)
    (hp : s.pc = 2) (ht : s.natReg 2447 = UniformBatching.threshold)
    (hk : UniformBatching.threshold ≤ s.natReg 2440)
    (hs : WordBound B s) (hb : Budget (s.natReg 2440) B) :
    BoundedRuns program n x B s 11 (recursiveStart s) := by
  rcases hb with ⟨hc,hthreshold,hkB,hR,hpow,hcount⟩
  have hm := constants_le_threshold.1.trans hthreshold
  have hrole := constants_le_threshold.2.trans hthreshold
  have hu := pc_bound s 3 B hs (by omega)
  have hpref := block_runs prepareOps program 3 n B x (setPC s 3) prepare_code rfl hu
    (by simp [prepareOps]; omega) (by simp [readable,prepareOps,Op.readable])
    (by simp [peak,prepareOps,Op.peak]; omega)
  let u := applyBlock prepareOps (setPC s 3)
  have hq : u.natReg 2440 / u.natReg 2448 ≤ B := by
    simpa [u,prepareOps,applyBlock,Op.apply,writeNat,next,setPC] using
      (Nat.div_le_self (s.natReg 2440) UniformBatching.blockSize).trans hkB
  let v := writeNat u 2441 (u.natReg 2440 / u.natReg 2448)
  have hv : WordBound B v := writeNat_bound B u 2441 _ hpref.final_bound
    (by simp [u,prepareOps,applyBlock,Op.apply,writeNat,next,setPC]; omega) hq
  have hpost := block_runs afterDivideOps program 9 n B x v after_divide_code
    (by simp [v,u,prepareOps,applyBlock,Op.apply,writeNat,next,setPC]) hv
    (by simp [afterDivideOps]; omega) (by simp [readable,afterDivideOps,Op.readable])
    (by
      have hK : v.natReg 2440 ≤ B := hv.2.1 2440
      simp [peak,afterDivideOps,Op.peak,Op.apply,writeNat,next]
      omega)
  have hdiv : step program n x u = .running v := by
    simp [step,program,u,v,prepareOps,applyBlock,Op.apply,writeNat,next,setPC,evalNat,
      Nat.ne_of_gt UniformBatching.blockSize_pos]
  have htail : BoundedRuns program n x B u 5 (applyBlock afterDivideOps v) :=
    .next hpref.final_bound hdiv hpost
  have hrun := hpref.trans htail
  apply BoundedRuns.next hs (u := setPC s 3)
  · simp [step,program,hp,ht,Nat.not_lt.mpr hk,setPC]
  · simpa [recursiveStart,u,v,prepareOps,afterDivideOps,applyBlock,Op.apply] using hrun

theorem round_bounded (n B : ℕ) (x : Fin n → ℂ) (s : State) (k i : ℕ)
    (h : Loop k i s) (hi : i < k - UniformBatching.quotient k - UniformBatching.roleBits)
    (hs : WordBound B s) (hb : Budget k B) :
    BoundedRuns program n x B s 4 (round s) := by
  rcases h with ⟨hp,hk,hq,he,hv,hit,hr,h1,h2⟩
  have heK : k - UniformBatching.quotient k - UniformBatching.roleBits ≤ k := by omega
  have hvalue : 2 ^ i * 2 ≤ B := by
    rw [← pow_succ]
    exact (Nat.pow_le_pow_right (by omega) (show i+1≤_ by omega)).trans hb.2.2.2.2.1
  have hu := pc_bound s 14 B hs (by have := hb.1; omega)
  have hblock := block_runs roundOps program 14 n B x (setPC s 14) round_code rfl hu
    (by simp [roundOps]; have := hb.1; omega)
    (by simp [readable,roundOps,Op.readable])
    (by simp [peak,roundOps,Op.peak,Op.apply,writeNat,next,setPC,hv,hit,h1,h2]
        have := hb.2.2.1; omega)
  have hjump : BoundedRuns program n x B (applyBlock roundOps (setPC s 14)) 1
      (round s) := by
    refine .next hblock.final_bound ?_ (.refl (pc_bound _ 13 B hblock.final_bound (by have := hb.1; omega)))
    simp [step,program,round,roundOps,applyBlock,Op.apply,setPC,writeNat,next]
  apply BoundedRuns.next hs (u := setPC s 14)
  · simp [step,program,hp,hit,he,hi,setPC]
  · simpa [roundOps] using hblock.trans hjump

theorem loop_halt_bounded (n B : ℕ) (x : Fin n → ℂ) (s : State) (k e : ℕ)
    (h : Loop k e s) (he : e = k - UniformBatching.quotient k - UniformBatching.roleBits)
    (hs : WordBound B s) (hb : Budget k B) :
    BoundedExecution program n x B s 5 (finish s) := by
  rcases h with ⟨hp,hk,hq,het,hv,hi,hr,h1,h2⟩
  have hu := pc_bound s 17 B hs (by have := hb.1; omega)
  have hblock := block_runs finishOps program 17 n B x (setPC s 17) finish_code rfl hu
    (by simp [finishOps]; have := hb.1; omega)
    (by simp [readable,finishOps,Op.readable])
    (by simp [peak,finishOps,Op.peak,setPC,hr,hv,he]; exact ⟨hb.2.2.2.2.2,by have := hb.1; omega⟩)
  let u := applyBlock finishOps (setPC s 17)
  have hv' := pc_bound u 24 B hblock.final_bound hb.1
  have hjump : BoundedExecution program n x B u 2 (finish s) := by
    refine .next hblock.final_bound ?_ (.halt hv' ?_)
    · simp [step,program,u,finishOps,applyBlock,Op.apply,setPC,writeNat,next,finish]
    · simp [step,program,finish,setPC,writeNat,next]
  apply BoundedExecution.next hs (u := setPC s 17)
  · simp [step,program,hp,hi,het,he,setPC]
  · simpa [u,finishOps] using hblock.executes hjump

theorem rounds_bounded (a : ℕ) (n B : ℕ) (x : Fin n → ℂ) (s : State) (k i : ℕ)
    (h : Loop k i s) (hi : i+a ≤ k-UniformBatching.quotient k-UniformBatching.roleBits)
    (hs : WordBound B s) (hb : Budget k B) :
    BoundedRuns program n x B s (4*a) (rounds a s) := by
  induction a generalizing s i with
  | zero => exact .refl hs
  | succ a ih =>
    have hr := round_bounded n B x s k i h (by omega) hs hb
    have ht := ih (round s) (i+1) (round_loop s k i h) (by omega) hr.final_bound
    simpa only [rounds,Nat.mul_succ,Nat.add_comm] using hr.trans ht

theorem recursive_bounded (n B : ℕ) (x : Fin n → ℂ) (s : State)
    (hp : s.pc = 0) (hk : UniformBatching.threshold ≤ s.natReg 2440)
    (hs : WordBound B s) (hb : Budget (s.natReg 2440) B) :
    BoundedExecution program n x B s
      (4*(s.natReg 2440-UniformBatching.quotient (s.natReg 2440)-UniformBatching.roleBits)+18)
      (recursiveFinal s) := by
  let k := s.natReg 2440
  let e := k-UniformBatching.quotient k-UniformBatching.roleBits
  have hboot := boot_bounded n B x s hp hs hb.1 hb.2.1
  have hprep := recursive_start_bounded n B x (boot s) (boot_pc s hp)
    (by simp [boot,writeNat,next]) (by simpa [boot,writeNat,next] using hk)
    hboot.final_bound (by simpa [boot,writeNat,next] using hb)
  have hloop := recursive_loop (boot s) k (by simp [boot,writeNat,next,k])
  have hr := rounds_bounded e n B x (recursiveStart (boot s)) k 0 hloop
    (by simp [e]) hprep.final_bound hb
  have hfinal := loop_halt_bounded n B x _ k e
    (by simpa using rounds_loop e _ k 0 hloop) rfl hr.final_bound hb
  have hex := (hboot.trans hprep).executes (hr.executes hfinal)
  have ht : (2+11)+(4*e+5)=4*e+18 := by omega
  rw [ht] at hex
  exact hex

theorem index_le_power (k : ℕ) : k ≤ 2^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 1 ≤ 2^k := by
      have h : 0 < 2^k := by positivity
      omega
    rw [pow_succ]
    nlinarith

theorem threshold_min : 24 ≤ UniformBatching.threshold := by
  norm_num [UniformBatching.threshold,UniformBatching.blockSize,UniformBatching.roleBits,
    ExplicitSeedBudget.m,ExplicitSeedBudget.roleBits]

/-- The true residual multiplicity fits within every large child volume. -/
theorem residuals_le_child_volume (k : ℕ) (hk : UniformBatching.threshold ≤ k) :
    ExplicitSeedBudget.residuals ≤ UniformBatching.width*2^UniformBatching.quotient k := by
  have hfixed : ExplicitSeedBudget.residuals ≤ UniformBatching.width*2^72 := by
    norm_num [ExplicitSeedBudget.residuals,UniformBatching.width,
      ExplicitSeedBudget.paddedRoles,ExplicitSeedBudget.roleBits]
  exact hfixed.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by norm_num) (UniformBatching.quotient_large hk)))

theorem child_count_le_volume (k : ℕ) (hk : UniformBatching.threshold ≤ k) :
    ExplicitSeedBudget.residuals*UniformBatching.batchCount k ≤ 2^k := by
  calc
    _ ≤ (UniformBatching.width*2^UniformBatching.quotient k)*UniformBatching.batchCount k :=
      Nat.mul_le_mul_right _ (residuals_le_child_volume k hk)
    _ = 2^k := by rw [Nat.mul_comm,UniformBatching.batch_partition hk]

/-- One volume bound suffices for every actual integer touched by dispatch. -/
theorem budget_from_volume (k B : ℕ) (hk : UniformBatching.threshold ≤ k)
    (hvolume : 2^k ≤ B) : Budget k B := by
  have hkB := (index_le_power k).trans hvolume
  have hthreshold := hk.trans hkB
  have hcount := (child_count_le_volume k hk).trans hvolume
  have hbatch : 1 ≤ UniformBatching.batchCount k := by
    unfold UniformBatching.batchCount
    have h : 0 < 2^(k-UniformBatching.quotient k-UniformBatching.roleBits) := by positivity
    omega
  have hR : ExplicitSeedBudget.residuals ≤ B := by
    nlinarith
  have hexponent : k-UniformBatching.quotient k-UniformBatching.roleBits ≤ k := by omega
  exact ⟨threshold_min.trans hthreshold,hthreshold,hkB,hR,
    (Nat.pow_le_pow_right (by norm_num) hexponent).trans hvolume,hcount⟩

def runtime (k : ℕ) : ℕ := if k<UniformBatching.threshold then 8 else
  4*(k-UniformBatching.quotient k-UniformBatching.roleBits)+18
def final (s : State) : State := if s.natReg 2440<UniformBatching.threshold then
  baseFinal (boot s) else recursiveFinal s

theorem execution (n B : ℕ) (x : Fin n → ℂ) (s : State)
    (hp : s.pc = 0) (hs : WordBound B s) (hc : 24 ≤ B)
    (ht : UniformBatching.threshold ≤ B) (hvolume : 2^s.natReg 2440 ≤ B) :
    BoundedExecution program n x B s (runtime (s.natReg 2440)) (final s) := by
  by_cases hk : s.natReg 2440<UniformBatching.threshold
  · simpa [runtime,final,hk] using base_bounded_from_entry n B x s hp hk hs hc ht
  · simpa [runtime,final,hk] using recursive_bounded n B x s hp
      (Nat.le_of_not_gt hk) hs (budget_from_volume _ B (Nat.le_of_not_gt hk) hvolume)

theorem runtime_linear (k : ℕ) : runtime k ≤ 4*k+18 := by
  unfold runtime
  split <;> omega

theorem frame_final (s : State) : Frame s (final s) := by
  unfold final
  split
  · exact (frame_boot s).trans (frame_base _)
  · exact frame_recursive_final s

/-- Child multiplicity is read from the actual post-state, not a ghost count. -/
theorem result_child_volume (s : State) (hk : UniformBatching.threshold ≤ s.natReg 2440) :
    (final s).natReg 2445 * (UniformBatching.width*2^((final s).natReg 2441)) =
      ExplicitSeedBudget.residuals*2^s.natReg 2440 := by
  have hr := recursive_result s
  simp only [final,ite_eq_right (Nat.not_lt.mpr hk)]
  rw [hr.1,hr.2.2.1]
  rw [Nat.mul_assoc,UniformBatching.batch_partition hk]

theorem result_mode (s : State) : (final s).natReg 2446 =
    if s.natReg 2440<UniformBatching.threshold then 0 else 1 := by
  by_cases hk : s.natReg 2440<UniformBatching.threshold
  · simp [final,hk,baseFinal,boot,setPC,writeNat,next]
  · simpa [final,hk] using (recursive_result s).2.2.2

theorem result_base (s : State) (hk : s.natReg 2440<UniformBatching.threshold) :
    (final s).natReg 2441=0 ∧ (final s).natReg 2443=0 ∧ (final s).natReg 2445=0 := by
  simp [final,hk,baseFinal,setPC,writeNat,next]

theorem canonical_constants (n : ℕ) (hn : 0<n) :
    24≤(n+2)^19 ∧ UniformBatching.threshold≤(n+2)^19 := by
  have hsmall : UniformBatching.threshold≤3^19 := by
    norm_num [UniformBatching.threshold,UniformBatching.blockSize,UniformBatching.roleBits,
      ExplicitSeedBudget.m,ExplicitSeedBudget.roleBits]
  have hm : 3^19≤(n+2)^19 := Nat.pow_le_pow_left (by omega) 19
  exact ⟨threshold_min.trans (hsmall.trans hm),hsmall.trans hm⟩

/-- Same canonical word budget; k and volume are actual caller headers. The
   dispatcher neither transforms data nor substitutes for the child scheduler. -/
theorem canonical_execution (n : ℕ) (hn : 0<n) (x : Fin n → ℂ) (s : State)
    (hp : s.pc=0) (hs : WordBound ((n+2)^19) s)
    (hvolume : 2^s.natReg 2440≤(n+2)^19) :
    BoundedExecution program n x ((n+2)^19) s (runtime (s.natReg 2440)) (final s) :=
  execution n _ x s hp hs (canonical_constants n hn).1 (canonical_constants n hn).2 hvolume

end
end ExactFourierCircuits.UniformRecursiveBatchHeaderMachine

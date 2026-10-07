import UniformWorkingCompletion
import UniformRoots
import Mathlib.Data.Nat.GCD.BigOperators

set_option autoImplicit false

namespace ExactFourierCircuits.UniformMasterRootMachine
open UniformMachine OAI.ExactFourier
noncomputable section

/-- Lcm of precisely the odd-prime entries of the selected table. -/
def oddLcm : ℕ → ℕ
  | 0 => 1
  | j + 1 => Nat.lcm (oddLcm j) (UniformWorkingLength.oddPrime j)

theorem oddLcm_product (j : ℕ) : oddLcm j = UniformWorkingLength.primeProduct j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hc : Nat.Coprime (UniformWorkingLength.primeProduct j) (UniformWorkingLength.oddPrime j) := by
      rw [UniformWorkingLength.primeProduct_eq_prod]
      apply Nat.coprime_prod_left_iff.mpr
      intro i hi
      exact UniformWorkingLength.oddPrime_coprime (by have h := Finset.mem_range.mp hi; omega)
    rw [oddLcm, ih, hc.lcm_eq_mul]
    rfl

def selectedLcm (n : ℕ) : ℕ :=
  Nat.lcm (oddLcm (UniformWorkingLength.axisCount n)) (UniformWorkingLength.binaryFactor n)

theorem selectedLcm_eq (n : ℕ) : selectedLcm n = UniformWorkingLength.workingLength n := by
  rw [selectedLcm, oddLcm_product]
  exact (UniformWorkingLength.oddProduct_coprime_binaryFactor n).lcm_eq_mul

theorem oddPrime_binary_coprime (n j : ℕ) :
    Nat.Coprime (UniformWorkingLength.oddPrime j) (UniformWorkingLength.binaryFactor n) :=
  (Nat.coprime_two_right.mpr (UniformWorkingLength.oddPrime_odd j)).pow_right _

/- Root workspace: target=19, power factor=20, exponent=21,
   twice-n=22, partial product=23, root order=24; constants16/2/1=25/26/27.
   Scalar register0 receives the only requested root. -/
def suffix : Program :=
  [.natLiteral 25 16, .natBinary .mul 19 17 25, .natLiteral 20 1, .natLiteral 21 0,
   .natLiteral 26 2, .natLiteral 27 1, .branchLT 20 19 53 56,
   .natBinary .mul 20 20 26, .natBinary .add 21 21 27, .jump 52,
   .natBinary .mul 22 8 26, .natBinary .mul 23 22 17, .natBinary .mul 24 23 20,
   .root 0 24, .halt]

def program : Program := UniformAssembly.embed [] UniformWorkingCompletion.program suffix 46

theorem preparation_code : UniformAssembly.CodeAt UniformWorkingCompletion.program program 0 46 :=
  UniformAssembly.embed_code [] UniformWorkingCompletion.program suffix 46

theorem program_length : program.length = 61 := by decide

theorem suffix_code (i : ℕ) : program[46 + i]? = suffix[i]? := by
  simp [program, UniformAssembly.embed, UniformWorkingCompletion.program_length,
    List.getElem?_append_right]

def Frame (s u : State) : Prop :=
  u.natHeap = s.natHeap ∧ u.scalarHeap = s.scalarHeap ∧ u.outputs = s.outputs ∧
    ∀ r, r < 19 ∨ 28 ≤ r → u.natReg r = s.natReg r

def LoopFrame (s u : State) : Prop := Frame s u ∧ u.scalarReg = s.scalarReg ∧ u.rootOrders = s.rootOrders

theorem loopFrame_refl (s : State) : LoopFrame s s :=
  ⟨⟨rfl, rfl, rfl, fun _ _ => rfl⟩, rfl, rfl⟩

theorem LoopFrame.trans {s u v : State} (h : LoopFrame s u) (h' : LoopFrame u v) : LoopFrame s v :=
  ⟨⟨h'.1.1.trans h.1.1, h'.1.2.1.trans h.1.2.1, h'.1.2.2.1.trans h.1.2.2.1,
    fun r hr => (h'.1.2.2.2 r hr).trans (h.1.2.2.2 r hr)⟩,
    h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩

def initialized (s : State) : State :=
  writeNat (writeNat (writeNat (writeNat (writeNat (writeNat s 25 16)
    19 (16 * s.natReg 17)) 20 1) 21 0) 26 2) 27 1

def Invariant (L e : ℕ) (s : State) : Prop :=
  s.pc = 52 ∧ s.natReg 19 = 16 * L ∧ s.natReg 20 = 2 ^ e ∧
    s.natReg 21 = e ∧ s.natReg 26 = 2 ∧ s.natReg 27 = 1

def powerState (s : State) : State := writeNat { s with pc := 53 } 20 (s.natReg 20 * 2)
def exponentState (s : State) : State := writeNat (powerState s) 21 (s.natReg 21 + 1)
def roundState (s : State) : State := { exponentState s with pc := 52 }

theorem phase_frames (s : State) : LoopFrame s (initialized s) ∧ LoopFrame s (roundState s) := by
  refine ⟨?_, ?_⟩
  all_goals refine ⟨⟨rfl, rfl, rfl, ?_⟩, rfl, rfl⟩
  all_goals intro r hr
  all_goals have h19 : r ≠ 19 := by omega
  all_goals have h20 : r ≠ 20 := by omega
  all_goals have h21 : r ≠ 21 := by omega
  all_goals have h25 : r ≠ 25 := by omega
  all_goals have h26 : r ≠ 26 := by omega
  all_goals have h27 : r ≠ 27 := by omega
  all_goals simp [initialized, roundState, exponentState, powerState, writeNat, next,
    h19, h20, h21, h25, h26, h27]

theorem initializes_bounded (B n L : ℕ) (x : Fin n → ℂ) (s : State)
    (hB : 61 ≤ B) (hLB : 32 * L ≤ B) (hb : WordBound B s) (hp : s.pc = 46)
    (hL : s.natReg 17 = L) : BoundedRuns program n x B s 6 (initialized s) := by
  have h46 := suffix_code 0
  have h47 := suffix_code 1
  have h48 := suffix_code 2
  have h49 := suffix_code 3
  have h50 := suffix_code 4
  have h51 := suffix_code 5
  have h1 := writeNat_bound B s 25 16 hb (by omega) (by omega)
  have h2 := writeNat_bound B (writeNat s 25 16) 19 (16 * s.natReg 17) h1
    (by simp [writeNat,next,hp]; omega) (by omega)
  have h3 := writeNat_bound B (writeNat (writeNat s 25 16) 19 (16 * s.natReg 17)) 20 1 h2
    (by simp [writeNat,next,hp]; omega) (by omega)
  have h4 := writeNat_bound B (writeNat (writeNat (writeNat s 25 16) 19 (16 * s.natReg 17)) 20 1) 21 0 h3
    (by simp [writeNat,next,hp]; omega) (by omega)
  have h5 := writeNat_bound B (writeNat (writeNat (writeNat (writeNat s 25 16) 19 (16 * s.natReg 17)) 20 1) 21 0) 26 2 h4
    (by simp [writeNat,next,hp]; omega) (by omega)
  have h6 := writeNat_bound B (writeNat (writeNat (writeNat (writeNat (writeNat s 25 16)
    19 (16 * s.natReg 17)) 20 1) 21 0) 26 2) 27 1 h5 (by simp [writeNat,next,hp]; omega) (by omega)
  refine .next hb (u := writeNat s 25 16) ?_
    (.next h1 (u := writeNat (writeNat s 25 16) 19 (16 * s.natReg 17)) ?_
      (.next h2 (u := writeNat (writeNat (writeNat s 25 16) 19 (16 * s.natReg 17)) 20 1) ?_
        (.next h3 (u := writeNat (writeNat (writeNat (writeNat s 25 16) 19 (16 * s.natReg 17)) 20 1) 21 0) ?_
          (.next h4 (u := writeNat (writeNat (writeNat (writeNat (writeNat s 25 16) 19 (16 * s.natReg 17)) 20 1) 21 0) 26 2) ?_
            (.next h5 (u := initialized s) ?_ (.refl h6))))))
  all_goals simp [step, evalNat, initialized, writeNat, next, hp, suffix,
    h46, h47, h48, h49, h50, h51, Nat.mul_comm]

theorem initialized_invariant (L : ℕ) (s : State) (hp : s.pc = 46) (hL : s.natReg 17 = L) :
    Invariant L 0 (initialized s) := by simp [Invariant,initialized,writeNat,next,hp,hL]

theorem round_invariant (L e : ℕ) (s : State) (hs : Invariant L e s) :
    Invariant L (e + 1) (roundState s) := by
  obtain ⟨_, h19, h20, h21, h26, h27⟩ := hs
  simp [Invariant,roundState,exponentState,powerState,writeNat,next,h19,h20,h21,h26,h27,pow_succ]

theorem round_bounded (B n L e : ℕ) (x : Fin n → ℂ) (s : State)
    (hB : 61 ≤ B) (hLB : 32 * L ≤ B) (hs : Invariant L e s) (hb : WordBound B s)
    (hgo : s.natReg 20 < 16 * L) : BoundedRuns program n x B s 4 (roundState s) := by
  obtain ⟨hp,h19,h20,h21,h26,h27⟩ := hs
  have hep : e < 2 ^ e := Nat.lt_pow_self (by decide)
  have h53 := changePC_bound B s 53 hb (by omega)
  have h54 := writeNat_bound B {s with pc:=53} 20 (s.natReg 20 * 2) h53 (by simp;omega) (by omega)
  have h55 := writeNat_bound B (powerState s) 21 (s.natReg 21 + 1) h54
    (by simp [powerState,writeNat,next];omega) (by omega)
  have h52 := changePC_bound B _ 52 h55 (by omega)
  have hc52 := suffix_code 6
  have hc53 := suffix_code 7
  have hc54 := suffix_code 8
  have hc55 := suffix_code 9
  refine .next hb (u:={s with pc:=53}) ?_
    (.next h53 (u:=powerState s) ?_ (.next h54 (u:=exponentState s) ?_
      (.next h55 (u:=roundState s) ?_ (.refl h52))))
  all_goals simp [step,evalNat,roundState,exponentState,powerState,writeNat,next,
    hp,h19,h26,h27,hgo,suffix,hc52,hc53,hc54,hc55]

theorem rootFactor_minimal (L e : ℕ) (he : e < UniformBatching.rootBits L) : 2 ^ e < 16 * L := by
  by_contra h
  have hl := UniformBatching.rootBits_le (by omega : 16 * L ≤ 2 ^ e)
  omega

/-- Proof-only induction fuel is absent from the bytecode. -/
theorem factor_bounded (B n L : ℕ) (x : Fin n → ℂ) (fuel e : ℕ) (s : State)
    (hB : 61 ≤ B) (hLB : 32 * L ≤ B) (he : e ≤ UniformBatching.rootBits L)
    (hf : UniformBatching.rootBits L - e + 1 ≤ fuel)
    (hs : Invariant L e s) (hb : WordBound B s) : ∃ u,
    BoundedRuns program n x B s (4 * (UniformBatching.rootBits L - e) + 1) u ∧
      u.pc = 56 ∧ u.natReg 20 = UniformBatching.rootFactor L ∧
      u.natReg 21 = UniformBatching.rootBits L ∧ u.natReg 26 = 2 ∧ LoopFrame s u := by
  induction fuel generalizing e s with
  | zero => omega
  | succ fuel ih =>
    by_cases hend : e = UniformBatching.rootBits L
    · obtain ⟨hp,h19,h20,h21,h26,_⟩ := hs
      have hstop : ¬s.natReg 20 < s.natReg 19 := by
        rw [h19,h20,hend]
        exact Nat.not_lt.mpr (UniformBatching.rootFactor_lower L)
      let u := {s with pc:=56}
      refine ⟨u, ?_, rfl, ?_, h21.trans hend, h26, loopFrame_refl s⟩
      · rw [hend,Nat.sub_self]
        refine .next hb (u:=u) ?_ (.refl (changePC_bound B s 56 hb (by omega)))
        simp [step,hp,suffix_code 6,suffix,hstop,u]
      · simpa [UniformBatching.rootFactor,hend] using h20
    · have hlt : e < UniformBatching.rootBits L := by omega
      have hgo : s.natReg 20 < 16 * L := by rw [hs.2.2.1];exact rootFactor_minimal L e hlt
      have hr := round_bounded B n L e x s hB hLB hs hb hgo
      obtain ⟨u,hu,hpc,h20,h21,h26,hframe⟩ := ih (e+1) (roundState s) (by omega)
        (by omega) (round_invariant L e s hs) hr.final_bound
      refine ⟨u, ?_, hpc,h20,h21,h26,(phase_frames s).2.trans hframe⟩
      convert hr.trans hu using 1; omega

def twiceState (s : State) : State := writeNat s 22 (2 * s.natReg 8)
def partialState (s : State) : State := writeNat (twiceState s) 23 (2 * s.natReg 8 * s.natReg 17)
def orderState (s : State) : State :=
  writeNat (partialState s) 24 (2 * s.natReg 8 * s.natReg 17 * s.natReg 20)
def provided (s : State) : State :=
  { writeScalar (orderState s) 0 ⟨zeta (2 * s.natReg 8 * s.natReg 17 * s.natReg 20), false⟩ with
    rootOrders := s.rootOrders ++ [2 * s.natReg 8 * s.natReg 17 * s.natReg 20] }

theorem provided_frame (s : State) : Frame s (provided s) ∧
    (provided s).rootOrders = s.rootOrders ++ [2 * s.natReg 8 * s.natReg 17 * s.natReg 20] ∧
    (provided s).scalarReg 0 = ⟨zeta (2 * s.natReg 8 * s.natReg 17 * s.natReg 20), false⟩ ∧
    (∀ r, r ≠ 0 → (provided s).scalarReg r = s.scalarReg r) := by
  refine ⟨⟨rfl,rfl,rfl,?_⟩,rfl,?_,?_⟩
  · intro r hr
    have h22 : r ≠ 22 := by omega
    have h23 : r ≠ 23 := by omega
    have h24 : r ≠ 24 := by omega
    simp [provided,orderState,partialState,twiceState,writeNat,writeScalar,next,h22,h23,h24]
  · simp [provided,writeScalar]
  · intro r hr; simp [provided,writeScalar,orderState,partialState,twiceState,writeNat,next,hr]

theorem tail_bounded (B n L : ℕ) (x : Fin n → ℂ) (s : State)
    (hB : 61 ≤ B) (hn : 0 < n) (hL : 0 < L) (hDB : UniformBatching.masterRootOrder n L ≤ B)
    (hb : WordBound B s) (hp : s.pc = 56) (h8 : s.natReg 8 = n) (h17 : s.natReg 17 = L)
    (h20 : s.natReg 20 = UniformBatching.rootFactor L) (h26 : s.natReg 26 = 2) :
    BoundedExecution program n x B s 5 (provided s) := by
  have hfactor : 1 ≤ UniformBatching.rootFactor L := by
    have h : 0 < UniformBatching.rootFactor L := by unfold UniformBatching.rootFactor; positivity
    omega
  have hpartial : 2 * n * L ≤ UniformBatching.masterRootOrder n L := by
    simpa [UniformBatching.masterRootOrder] using Nat.mul_le_mul_left (2 * n * L) hfactor
  have hnD : 2 * n ≤ UniformBatching.masterRootOrder n L :=
    (show 2 * n ≤ 2 * n * L by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 * n) (show 1 ≤ L by omega)).trans hpartial
  have hD : 0 < UniformBatching.masterRootOrder n L := UniformBatching.masterRootOrder_pos hn hL
  have heq : 2 * s.natReg 8 * s.natReg 17 * s.natReg 20 = UniformBatching.masterRootOrder n L := by
    rw [h8,h17,h20];rfl
  have h57 := writeNat_bound B s 22 (2 * s.natReg 8) hb (by omega) (by rw [h8];exact hnD.trans hDB)
  have h58 := writeNat_bound B (twiceState s) 23 (2 * s.natReg 8 * s.natReg 17) h57
    (by simp [twiceState,writeNat,next,hp];omega) (by rw [h8,h17];exact hpartial.trans hDB)
  have h59 := writeNat_bound B (partialState s) 24
    (2 * s.natReg 8 * s.natReg 17 * s.natReg 20) h58
    (by simp [partialState,twiceState,writeNat,next,hp];omega) (by rw [heq];exact hDB)
  have hscalar := writeScalar_bound B (orderState s) 0
    ⟨zeta (2 * s.natReg 8 * s.natReg 17 * s.natReg 20),false⟩ h59
    (by simp [orderState,partialState,twiceState,writeNat,next,hp];omega)
  have hroot : WordBound B (provided s) := by
    refine ⟨hscalar.1,hscalar.2.1,hscalar.2.2.1,hscalar.2.2.2.1,hscalar.2.2.2.2.1,?_⟩
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hb.2.2.2.2.2 d hd
    · simp only [List.mem_singleton] at hd
      rw [hd,heq];exact hDB
  have hc56 := suffix_code 10
  have hc57 := suffix_code 11
  have hc58 := suffix_code 12
  have hc59 := suffix_code 13
  have hc60 := suffix_code 14
  refine .next hb (u:=twiceState s) ?_ (.next h57 (u:=partialState s) ?_
    (.next h58 (u:=orderState s) ?_ (.next h59 (u:=provided s) ?_ (.halt hroot ?_))))
  all_goals simp [step,evalNat,provided,orderState,partialState,twiceState,writeNat,writeScalar,next,
    hp,h26,heq,hD.ne',suffix,hc56,hc57,hc58,hc59,hc60,Nat.mul_comm]

theorem wordBound_setup {n : ℕ} (hn : 0 < n) :
    (n + 2) ^ 9 ≤ (n + 2) ^ 12 ∧ 61 ≤ (n + 2) ^ 12 ∧
    128 * n ≤ (n + 2) ^ 12 ∧ 1024 * n ^ 3 ≤ (n + 2) ^ 12 := by
  have hp3 : 1 ≤ (n + 2) ^ 3 := by
    simpa only [Nat.one_pow] using Nat.pow_le_pow_left (show 1 ≤ n + 2 by omega) 3
  have hp9 : 19683 ≤ (n + 2) ^ 9 := by
    have h := Nat.pow_le_pow_left (show 3 ≤ n + 2 by omega) 9
    norm_num at h;exact h
  have h9 : (n + 2) ^ 9 ≤ (n + 2) ^ 12 := by
    calc
      (n+2)^9 ≤ (n+2)^9*(n+2)^3 := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((n+2)^9) hp3
      _ = (n+2)^12 := by rw [←pow_add]
  have h128 : 128*n ≤ (n+2)^12 := by
    have hp : 128 ≤ (n+2)^9 := by omega
    have hn3 : n ≤ (n+2)^3 := by
      have hp2 : 1 ≤ (n+2)^2 := by
        simpa only [Nat.one_pow] using Nat.pow_le_pow_left (show 1 ≤ n+2 by omega) 2
      calc
        n ≤ n+2 := by omega
        _ ≤ (n+2)*(n+2)^2 := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (n+2) hp2
        _ = (n+2)^3 := by simpa [Nat.mul_comm] using (pow_succ (n+2) 2).symm
    calc
      128*n ≤ (n+2)^9*(n+2)^3 := Nat.mul_le_mul hp hn3
      _ = (n+2)^12 := by rw [←pow_add]
  have h1024 : 1024*n^3 ≤ (n+2)^12 := by
    calc
      1024*n^3 ≤ (n+2)^9*(n+2)^3 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 3)
      _ = (n+2)^12 := by rw [←pow_add]
  exact ⟨h9,by omega,h128,h1024⟩

theorem Frame.prepared {n : ℕ} {s u : State} (hf : Frame s u)
    (hs : UniformWorkingCompletion.PreparedState n s) : UniformWorkingCompletion.PreparedState n u := by
  obtain ⟨⟨h0,h10,h11,ht,hh⟩,h16,h18,h17⟩ := hs
  refine ⟨⟨(hf.2.2.2 0 (by simp)).trans h0,(hf.2.2.2 10 (by simp)).trans h10,
    (hf.2.2.2 11 (by simp)).trans h11,?_,?_⟩,
    (hf.2.2.2 16 (by simp)).trans h16,(hf.2.2.2 18 (by simp)).trans h18,
    (hf.2.2.2 17 (by simp)).trans h17⟩
  · simpa [UniformWorkingMachine.PrimeTable,hf.1] using ht
  · simpa [hf.1] using hh

theorem Frame.trans {s u v : State} (h : Frame s u) (h' : Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    fun r hr => (h'.2.2.2 r hr).trans (h.2.2.2 r hr)⟩

def order (n : ℕ) : ℕ := UniformBatching.masterRootOrder n (UniformWorkingLength.workingLength n)

theorem order_bounds {n : ℕ} (hn : 0 < n) : 0 < order n ∧ order n < 1024 * n ^ 3 :=
  ⟨UniformBatching.masterRootOrder_pos hn (UniformWorkingLength.workingLength_pos hn),
    UniformWorkingLength.selected_masterRoot_bound hn⟩

theorem order_paper_formula (n : ℕ) : order n = (2 * n) * selectedLcm n *
    2 ^ ⌈Real.logb 2 ((16 * UniformWorkingLength.workingLength n : ℕ) : ℝ)⌉₊ := by
  rw [selectedLcm_eq,←UniformBatching.rootBits_ceil]
  rfl

def MasterState (n : ℕ) (u : State) : Prop :=
  UniformWorkingCompletion.PreparedState n u ∧ u.natReg 24 = order n ∧
    u.natReg 20 = UniformBatching.rootFactor (UniformWorkingLength.workingLength n) ∧
    u.natReg 21 = UniformBatching.rootBits (UniformWorkingLength.workingLength n) ∧
    u.scalarReg 0 = ⟨zeta (order n),false⟩ ∧ u.rootOrders = [order n]

def preparationBudget (n : ℕ) : ℕ := UniformWorkingCompletion.preparationBudget n +
  4 * UniformBatching.rootBits (UniformWorkingLength.workingLength n) + 12

/-- One fixed program prepares the actual working length/table and requests exactly
    one root of the paper's specified order. No input scalars have been read. -/
theorem master_execution {n : ℕ} (hn : 0 < n) (x : Fin n → ℂ) : ∃ t u,
    BoundedExecution program n x ((n+2)^12) initial t u ∧ MasterState n u ∧
      u.pc=60 ∧ u.natReg 8=n ∧ u.scalarHeap=initial.scalarHeap ∧ u.outputs=initial.outputs ∧
      (∀ r, r ≠ 0 → u.scalarReg r=initial.scalarReg r) ∧ t ≤ preparationBudget n := by
  obtain ⟨hpreB,hB,h128B,hDB⟩ := wordBound_setup hn
  obtain ⟨t,v,hv,hprepared,_,h8,hs,hh,ho,hd,hcost⟩ := UniformWorkingCompletion.preparation_execution hn x
  have hLpos := UniformWorkingLength.workingLength_pos hn
  have hLupper := UniformWorkingLength.workingLength_upper hn
  have hLB : 32 * UniformWorkingLength.workingLength n ≤ (n+2)^12 := by omega
  have horderB : order n ≤ (n+2)^12 := (Nat.le_of_lt (order_bounds hn).2).trans hDB
  have hvB := UniformWorkingMachine.boundedExecution_mono hpreB hv
  have hprefix : BoundedRuns program n x ((n+2)^12) initial t {v with pc:=46} := by
    have h := UniformAssembly.BoundedExecution.placed preparation_code
      (by omega : 0+(n+2)^12≤(n+2)^12) (by omega : 46≤(n+2)^12) hvB
    simpa [UniformAssembly.placed,initial] using h
  let entry := {v with pc:=46}
  have hL : entry.natReg 17 = UniformWorkingLength.workingLength n := hprepared.2.2.2
  have hinit := initializes_bounded ((n+2)^12) n (UniformWorkingLength.workingLength n) x
    entry hB hLB hprefix.final_bound rfl hL
  obtain ⟨w,hw,hpc,h20,h21,h26,hloop⟩ := factor_bounded ((n+2)^12) n
    (UniformWorkingLength.workingLength n) x (UniformBatching.rootBits (UniformWorkingLength.workingLength n)+1)
    0 (initialized entry) hB hLB (by omega) (by omega)
    (initialized_invariant _ entry rfl hL) hinit.final_bound
  have hframe : LoopFrame entry w := (phase_frames entry).1.trans hloop
  have hw8 : w.natReg 8=n := (hframe.1.2.2.2 8 (by simp)).trans h8
  have hw17 : w.natReg 17=UniformWorkingLength.workingLength n :=
    (hframe.1.2.2.2 17 (by simp)).trans hL
  have htail := tail_bounded ((n+2)^12) n (UniformWorkingLength.workingLength n) x w hB hn
    hLpos horderB hw.final_bound hpc hw8 hw17 h20 h26
  have hraw : 2*w.natReg 8*w.natReg 17*w.natReg 20=order n := by rw [hw8,hw17,h20];rfl
  have hfinalframe : Frame entry (provided w) := hframe.1.trans (provided_frame w).1
  refine ⟨t+6+(4*UniformBatching.rootBits (UniformWorkingLength.workingLength n)+1)+5,
    provided w,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.sub_zero] using ((hprefix.trans hinit).trans hw).executes htail
  · refine ⟨hfinalframe.prepared hprepared,?_,?_,?_,?_,?_⟩
    · simp [provided,orderState,writeNat,writeScalar,next,hraw]
    · simpa [provided,orderState,partialState,twiceState,writeNat,writeScalar,next] using h20
    · simpa [provided,orderState,partialState,twiceState,writeNat,writeScalar,next] using h21
    · simpa [hraw] using (provided_frame w).2.2.1
    · rw [(provided_frame w).2.1,hframe.2.2,hd,hraw];rfl
  · simp [provided,orderState,partialState,twiceState,writeNat,writeScalar,next,hpc]
  · exact (hfinalframe.2.2.2 8 (by simp)).trans h8
  · exact hfinalframe.2.1.trans hh
  · exact hfinalframe.2.2.1.trans ho
  · intro r hr
    rw [(provided_frame w).2.2.2 r hr,hframe.2.1,hs]
  · dsimp [preparationBudget,UniformWorkingCompletion.preparationBudget]
    omega

theorem root_factor_bounds {n : ℕ} (hn : 0 < n) {u : State} (hu : MasterState n u) :
    16*UniformWorkingLength.workingLength n ≤ u.natReg 20 ∧
      u.natReg 20 < 32*UniformWorkingLength.workingLength n := by
  rw [hu.2.2.1]
  exact ⟨UniformBatching.rootFactor_lower _,UniformBatching.rootFactor_upper (UniformWorkingLength.workingLength_pos hn)⟩

theorem divisor_orders (n : ℕ) : 2*n ∣ order n ∧ UniformWorkingLength.workingLength n ∣ order n ∧
    UniformWorkingLength.binaryFactor n ∣ order n ∧
    ∀ i, i<UniformWorkingLength.axisCount n → UniformWorkingLength.oddPrime i ∣ order n := by
  refine ⟨UniformBatching.chirpOrder_dvd _ _,UniformBatching.workingOrder_dvd _ _,?_,?_⟩
  · exact (Nat.dvd_mul_left (UniformWorkingLength.binaryFactor n) (UniformWorkingLength.oddProduct n)).trans
      (UniformBatching.workingOrder_dvd n (UniformWorkingLength.workingLength n))
  · intro i hi
    have hprod : UniformWorkingLength.oddPrime i ∣ UniformWorkingLength.oddProduct n := by
      rw [UniformWorkingLength.oddProduct,UniformWorkingLength.primeProduct_eq_prod]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hi)
    exact (hprod.trans (Nat.dvd_mul_right (UniformWorkingLength.oddProduct n)
      (UniformWorkingLength.binaryFactor n))).trans (UniformBatching.workingOrder_dvd _ _)

theorem localPowerOrder_dvd {n r e : ℕ} (hr : r ≤ UniformWorkingLength.workingLength n)
    (he : 2^e ≤ 8*r) : 2^e ∣ order n := UniformBatching.localPowerOrder_dvd hr he

/-- Exact specified phase, not merely an arbitrary primitive root.
    Executing this power is a separate charged PowerMachine phase. -/
theorem specified_divisor_root {n : ℕ} (hn : 0<n) {u : State} (hu : MasterState n u)
    (d : ℕ) (hd : 0<d) (hdiv : d ∣ order n) :
    (u.scalarReg 0).value ^ (order n/d)=zeta d ∧ (u.scalarReg 0).dependent=false := by
  rw [hu.2.2.2.2.1]
  exact ⟨UniformRoots.specifiedRoot_divisor_power _ _ (order_bounds hn).1 hd hdiv,rfl⟩

theorem rootBits_log_bound {n : ℕ} (hn : 0<n) :
    UniformBatching.rootBits (UniformWorkingLength.workingLength n) ≤ Nat.clog 2 (64*n) := by
  have h := UniformWorkingLength.workingLength_upper hn
  exact Nat.clog_mono_right 2 (by omega)

def rootBudget (n : ℕ) : ℕ := 4 * UniformBatching.rootBits (UniformWorkingLength.workingLength n) + 12

theorem rootBudget_isBigO_log :
    (fun n : ℕ => (rootBudget n : ℝ)) =O[Filter.atTop] (fun n : ℕ => Real.log (n : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 64
  have htlog : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_ge_atTop (1:ℕ),
    htlog.eventually (Filter.eventually_ge_atTop (1:ℝ))] with n hn hlog
  have hnpos : 0<n := by omega
  have hlogclog : (Nat.clog 2 (64*n) : ℝ) ≤ Real.logb 2 ((64*n:ℕ):ℝ)+1 := by
    have hnonneg : 0 ≤ Real.logb 2 ((64*n:ℕ):ℝ) :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ 64*n by omega))
    have hc := Nat.ceil_lt_add_one hnonneg
    calc
      (Nat.clog 2 (64*n) : ℝ) = (⌈Real.logb 2 ((64*n:ℕ):ℝ)⌉₊ : ℝ) := by
        exact congrArg (fun k:ℕ => (k:ℝ)) (Real.natCeil_logb_natCast 2 (64*n)).symm
      _ ≤ Real.logb 2 ((64*n:ℕ):ℝ)+1 := hc.le
  have hbits : (UniformBatching.rootBits (UniformWorkingLength.workingLength n) : ℝ) ≤
      Real.logb 2 ((64*n:ℕ):ℝ)+1 :=
    (show (UniformBatching.rootBits (UniformWorkingLength.workingLength n) : ℝ) ≤
      (Nat.clog 2 (64*n) : ℝ) by exact_mod_cast rootBits_log_bound hnpos).trans hlogclog
  have hlog64 : Real.log (64:ℝ)=6*Real.log 2 := by
    rw [show (64:ℝ)=(2:ℝ)^6 by norm_num,Real.log_pow]
    norm_num
  have hmul : Real.log ((64*n:ℕ):ℝ)=Real.log (64:ℝ)+Real.log (n:ℝ) := by
    push_cast
    exact Real.log_mul (by norm_num) (Nat.cast_ne_zero.mpr hnpos.ne')
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2low := UniformWorkingLength.log_two_lower
  have hfrac : (6*Real.log 2+Real.log (n:ℝ))/Real.log 2 ≤ 6+2*Real.log (n:ℝ) := by
    apply (div_le_iff₀ h2).2
    have hm := mul_nonneg (by linarith : 0 ≤ Real.log (n:ℝ))
      (by linarith : 0 ≤ 2*Real.log 2-1)
    nlinarith
  rw [Real.logb,hmul,hlog64] at hbits
  have hreal : (rootBudget n : ℝ) ≤ 64*Real.log (n:ℝ) := by
    dsimp [rootBudget]
    push_cast
    linarith
  simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (by linarith : 0 ≤ Real.log (n:ℝ))] using hreal

theorem preparationBudget_isLittleO_input :
    (fun n : ℕ => (preparationBudget n : ℝ)) =o[Filter.atTop] (fun n : ℕ => (n : ℝ)) := by
  have hlog : (fun n : ℕ => Real.log (n:ℝ)) =o[Filter.atTop] (fun n : ℕ => (n:ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hroot := rootBudget_isBigO_log.trans_isLittleO hlog
  have hsum := UniformWorkingCompletion.preparationBudget_isLittleO_input.add hroot
  simpa [preparationBudget,rootBudget,Nat.cast_add,add_assoc] using hsum

end
end ExactFourierCircuits.UniformMasterRootMachine

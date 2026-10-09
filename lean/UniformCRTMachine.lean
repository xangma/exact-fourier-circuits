import UniformCRT
import UniformMachineRuns

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2, CRT tables and linear index traversal surrounding (5.5),
PDF p.22 (`eq:crt-fourier`), using the prefix bound (4.1), PDF p.18.

Literal integer/table/traversal bookkeeping refines that argument. The paper
does not specify this register layout or these frames; semantic and charged
execution obligations are separate declarations below.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCRTMachine
open UniformMachine

/-- Explicit candidate scanning, with no inverse or coprimality oracle. -/
structure Result where
  digit : ℕ
  steps : ℕ
  deriving Repr

def failedProbeCost (r : ℕ) : ℕ := if r < 1 then 6 else 7

def scanLoop (a q : ℕ) : ℕ → ℕ → Result
  | 0, d => ⟨d,2⟩
  | f+1, d =>
    if a*d % q = 1 then ⟨d,6⟩ else
      let tail := scanLoop a q f (d+1)
      ⟨tail.digit, failedProbeCost (a*d % q)+tail.steps⟩

def scan (a q : ℕ) : Result := scanLoop a q q 0

theorem failedProbeCost_bound (r : ℕ) : failedProbeCost r ≤ 7 := by
  unfold failedProbeCost; split_ifs <;> omega

theorem scanLoop_cost (a q f d : ℕ) : (scanLoop a q f d).steps ≤ 7*f+6 := by
  induction f generalizing d with
  | zero => simp [scanLoop]
  | succ f ih =>
    simp only [scanLoop]
    split_ifs
    · simp
    · have h := ih (d+1)
      have hc := failedProbeCost_bound (a*d%q)
      dsimp; omega

theorem inverse_value_spec (a q : ℕ) (hq : 1 < q) (hc : Nat.Coprime a q) :
    a*((a : ZMod q)⁻¹).val % q = 1 := by
  let : NeZero q := ⟨by omega⟩
  have h : ((a*((a : ZMod q)⁻¹).val : ℕ) : ZMod q) = ((1:ℕ):ZMod q) := by
    simpa only [Nat.cast_mul,Nat.cast_one] using ZMod.mul_val_inv hc
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hq] using congrArg ZMod.val h

theorem inverse_unique (a q d : ℕ) (hq : 1 < q) (hc : Nat.Coprime a q)
    (hd : d < q) (hm : a*d%q = 1) : d = ((a : ZMod q)⁻¹).val := by
  let : NeZero q := ⟨by omega⟩
  let w := ((a : ZMod q)⁻¹).val
  have hw : w < q := ZMod.val_lt _
  have h1 : (a : ZMod q)*(w : ZMod q) = 1 := ZMod.mul_val_inv hc
  have hz : (a : ZMod q)*(d : ZMod q) = 1 := by
    rw [← Nat.cast_mul, ← ZMod.natCast_mod (a*d), hm]; norm_num
  have he : (d : ZMod q) = (w : ZMod q) := calc
    (d : ZMod q) = ((w : ZMod q)*(a : ZMod q))*d := by rw [mul_comm (w : ZMod q),h1,one_mul]
    _ = (w : ZMod q)*((a : ZMod q)*d) := mul_assoc _ _ _
    _ = (w : ZMod q) := by rw [hz,mul_one]
  simpa [ZMod.val_natCast,Nat.mod_eq_of_lt hd,Nat.mod_eq_of_lt hw] using congrArg ZMod.val he

theorem scanLoop_correct (a q : ℕ) (hq : 1 < q) (hc : Nat.Coprime a q)
    (f d : ℕ) (hcap : d+f ≤ q)
    (hlo : d ≤ ((a : ZMod q)⁻¹).val) (hhi : ((a : ZMod q)⁻¹).val < d+f) :
    (scanLoop a q f d).digit = ((a : ZMod q)⁻¹).val := by
  induction f generalizing d with
  | zero => omega
  | succ f ih =>
    simp only [scanLoop]
    split_ifs with hm
    · exact inverse_unique a q d hq hc (by omega) hm
    · have hlt : d < ((a : ZMod q)⁻¹).val := by
        by_contra h
        have he : d = ((a : ZMod q)⁻¹).val := by omega
        exact hm (he ▸ inverse_value_spec a q hq hc)
      exact ih (d+1) (by omega) (by omega) (by omega)

theorem scan_correct (a q : ℕ) (hq : 1 < q) (hc : Nat.Coprime a q) :
    (scan a q).digit = ((a : ZMod q)⁻¹).val := by
  let : NeZero q := ⟨by omega⟩
  exact scanLoop_correct a q hq hc q 0 (by omega) (by omega) (by simpa using ZMod.val_lt ((a : ZMod q)⁻¹))

/-- Input Nat registers: 0=a, 1=q. Output register: 3=inverse digit.
Equality with one is implemented by two ordinary Nat comparisons. -/
def program : Program := [
  .natLiteral 2 1, .natLiteral 3 0,
  .branchLT 3 1 3 10,
  .natBinary .mul 4 0 3, .natBinary .mod 5 4 1,
  .branchLT 5 2 8 6, .branchLT 2 5 8 10,
  .jump 10, .natBinary .add 3 3 2, .jump 2, .halt]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual table selector handles a width-one identity factor directly. -/
def crtDigit (r : ι → ℕ) (i : ι) : ℕ :=
  if r i = 1 then 0 else (scan (UniformCRT.cofactor r i) (r i)).digit

noncomputable section

def initialized (s : State) : State := writeNat (writeNat s 2 1) 3 0

def probeStart (s : State) : State := {s with pc := 3}
def productState (s : State) : State := writeNat (probeStart s) 4 (s.natReg 0*s.natReg 3)
def residueState (s : State) : State := writeNat (productState s) 5 (s.natReg 0*s.natReg 3%s.natReg 1)
def failedState (s : State) : State :=
  {writeNat {residueState s with pc := 8} 3 (s.natReg 3+1) with pc := 2}
def matchedState (s : State) : State := {residueState s with pc := 10}


def Context (a q d : ℕ) (s : State) : Prop :=
  s.pc = 2 ∧ s.natReg 0 = a ∧ s.natReg 1 = q ∧ s.natReg 2 = 1 ∧ s.natReg 3 = d

def Frame (s u : State) : Prop :=
  u.scalarReg = s.scalarReg ∧ u.natHeap = s.natHeap ∧
  u.scalarHeap = s.scalarHeap ∧ u.outputs = s.outputs ∧ u.rootOrders = s.rootOrders

theorem frame_trans (s u v : State) (h : Frame s u) (h' : Frame u v) : Frame s v := by
  rcases h with ⟨h1,h2,h3,h4,h5⟩
  rcases h' with ⟨h1',h2',h3',h4',h5'⟩
  exact ⟨h1'.trans h1,h2'.trans h2,h3'.trans h3,h4'.trans h4,h5'.trans h5⟩

theorem probe_runs (n : ℕ) (x : Fin n → ℂ) (a q d : ℕ) (s : State)
    (hq : 0 < q) (hd : d < q) (hs : Context a q d s) :
    Runs program n x s 3 (residueState s) := by
  rcases hs with ⟨hp,ha,hq',h1,hd'⟩
  refine .next (u := probeStart s) ?_ (.next (u := productState s) ?_ (.next ?_ (.refl _)))
  all_goals simp [step,program,probeStart,productState,residueState,writeNat,next,
    hp,ha,hq',hd',hd,hq.ne',evalNat]

theorem failed_runs (n : ℕ) (x : Fin n → ℂ) (a q d : ℕ) (s : State)
    (hs : Context a q d s) (hm : a*d%q ≠ 1) :
    Runs program n x (residueState s) (failedProbeCost (a*d%q)-3) (failedState s) := by
  rcases hs with ⟨hp,ha,hq',h1,hd'⟩
  by_cases hz : a*d%q < 1
  · simp only [failedProbeCost,ite_eq_left hz]
    refine .next (u := {residueState s with pc := 8}) ?_
      (.next (u := writeNat {residueState s with pc := 8} 3 (s.natReg 3+1)) ?_
      (.next ?_ (.refl _)))
    all_goals simp [step,program,probeStart,productState,residueState,failedState,
      writeNat,next,ha,hq',h1,hd',hz,evalNat]
  · have hg : 1 < a*d%q := by omega
    simp only [failedProbeCost,ite_eq_right hz]
    refine .next (u := {residueState s with pc := 6}) ?_
      (.next (u := {residueState s with pc := 8}) ?_
      (.next (u := writeNat {residueState s with pc := 8} 3 (s.natReg 3+1)) ?_
      (.next ?_ (.refl _))))
    all_goals simp [step,program,probeStart,productState,residueState,failedState,
      writeNat,next,ha,hq',h1,hd',hz,hg,evalNat]

theorem matched_executes (n : ℕ) (x : Fin n → ℂ) (a q d : ℕ) (s : State)
    (hs : Context a q d s) (hm : a*d%q = 1) :
    Executes program n x (residueState s) 3 (matchedState s) := by
  rcases hs with ⟨hp,ha,hq',h1,hd'⟩
  refine .next (u := {residueState s with pc := 6}) ?_ (.next ?_ (.halt ?_))
  all_goals simp [step,program,probeStart,productState,residueState,matchedState,
    writeNat,next,ha,hq',h1,hd',hm]

theorem failed_context (a q d : ℕ) (s : State) (hs : Context a q d s) :
    Context a q (d+1) (failedState s) ∧ Frame s (failedState s) := by
  rcases hs with ⟨hp,ha,hq',h1,hd⟩
  simp [Context,Frame,failedState,residueState,productState,probeStart,writeNat,next,
    ha,hq',h1,hd]

theorem matched_frame (s : State) : Frame s (matchedState s) ∧
    (matchedState s).natReg 3 = s.natReg 3 := by
  simp [Frame,matchedState,residueState,productState,probeStart,writeNat,next]

theorem loop_execution (n : ℕ) (x : Fin n → ℂ) (a q f d : ℕ) (s : State)
    (hq : 0 < q) (hcap : d+f = q) (hs : Context a q d s) :
    ∃ u : State, Executes program n x s (scanLoop a q f d).steps u ∧
      u.natReg 3 = (scanLoop a q f d).digit ∧ Frame s u := by
  induction f generalizing s d with
  | zero =>
    have hd : d = q := by omega
    refine ⟨{s with pc := 10},?_,?_,?_⟩
    · refine .next ?_ (.halt ?_)
      · simp [step,program,hs.1,hs.2.2.1,hs.2.2.2.2,hd]
      · simp [step,program]
    · simpa [scanLoop] using hs.2.2.2.2
    · simp [Frame]
  | succ f ih =>
    have hd : d < q := by omega
    have hprobe := probe_runs n x a q d s hq hd hs
    rw [scanLoop]
    split_ifs with hm
    · refine ⟨matchedState s,?_,?_,(matched_frame s).1⟩
      · exact hprobe.executes (matched_executes n x a q d s hs hm)
      · simpa using (matched_frame s).2.trans hs.2.2.2.2
    · have hfail := failed_runs n x a q d s hs hm
      obtain ⟨u,hu,hdigit,hframe⟩ := ih (d+1) (failedState s) (by omega) (failed_context a q d s hs).1
      refine ⟨u,?_,hdigit,frame_trans s _ u (failed_context a q d s hs).2 hframe⟩
      have he := (hprobe.trans hfail).executes hu
      have hfc : 3 ≤ failedProbeCost (a*d%q) := by unfold failedProbeCost; split_ifs <;> omega
      convert he using 1; dsimp; omega


def Counters (a q : ℕ) (s : State) : Prop :=
  2 ≤ s.pc ∧ s.pc ≤ 10 ∧ s.natReg 0 = a ∧ s.natReg 1 = q ∧ s.natReg 2 = 1 ∧
  s.natReg 3 ≤ q ∧ (3 ≤ s.pc → s.pc ≤ 8 → s.natReg 3 < q)

def Interior (a q B : ℕ) (s : State) : Prop := WordBound B s ∧ Counters a q s

theorem step_interior (n : ℕ) (x : Fin n → ℂ) (a q B : ℕ) (s u : State)
    (hq : 0 < q) (hB : a*q+a+q+11 ≤ B) (hs : Interior a q B s)
    (h : step program n x s = .running u) : Interior a q B u := by
  obtain ⟨hb,hlo,hhi,ha,hq',h1,hd,hstrict⟩ := hs
  have hpc : s.pc+1 ≤ B := by omega
  have hnat (r v : ℕ) (hv : v ≤ B) := writeNat_bound B s r v hb hpc hv
  have hstrict' : s.pc < 3 ∨ 8 < s.pc ∨ s.natReg 3 < q := by
    by_cases hlo : 3 ≤ s.pc
    · by_cases hhi : s.pc ≤ 8
      · exact Or.inr (Or.inr (hstrict hlo hhi))
      · exact Or.inr (Or.inl (by omega))
    · exact Or.inl (by omega)
  interval_cases hp : s.pc
  · by_cases he : s.natReg 3 < q
    · simp [step,program,hp,hq',he] at h; subst u
      refine ⟨changePC_bound B s 3 hb (by omega), ?_⟩
      simp [Counters]; omega
    · simp [step,program,hp,hq',he] at h; subst u
      refine ⟨changePC_bound B s 10 hb (by omega), ?_⟩
      simp [Counters]; omega
  · simp [step,program,hp,ha,evalNat] at h; subst u
    have hmul := Nat.mul_le_mul_left a hd
    refine ⟨hnat 4 (a*s.natReg 3) (by omega), ?_⟩
    simp [Counters,writeNat,next,hp]; omega
  · simp [step,program,hp,hq',hq.ne',evalNat] at h; subst u
    have hmod := Nat.mod_lt (s.natReg 4) hq
    refine ⟨hnat 5 (s.natReg 4%q) (by omega), ?_⟩
    simp [Counters,writeNat,next,hp]; omega
  · by_cases he : s.natReg 5 < s.natReg 2
    · simp [step,program,hp,he] at h; subst u
      refine ⟨changePC_bound B s 8 hb (by omega), ?_⟩
      simp [Counters]; omega
    · simp [step,program,hp,he] at h; subst u
      refine ⟨changePC_bound B s 6 hb (by omega), ?_⟩
      simp [Counters]; omega
  · by_cases he : s.natReg 2 < s.natReg 5
    · simp [step,program,hp,he] at h; subst u
      refine ⟨changePC_bound B s 8 hb (by omega), ?_⟩
      simp [Counters]; omega
    · simp [step,program,hp,he] at h; subst u
      refine ⟨changePC_bound B s 10 hb (by omega), ?_⟩
      simp [Counters]; omega
  · simp [step,program,hp] at h; subst u
    refine ⟨changePC_bound B s 10 hb (by omega), ?_⟩
    simp [Counters]; omega
  · simp [step,program,hp,h1,evalNat] at h; subst u
    refine ⟨hnat 3 (s.natReg 3+1) (by omega), ?_⟩
    simp [Counters,writeNat,next,hp]; omega
  · simp [step,program,hp] at h; subst u
    refine ⟨changePC_bound B s 2 hb (by omega), ?_⟩
    simp [Counters]; omega
  · simp [step,program,hp] at h

theorem startup_bounded (n : ℕ) (x : Fin n → ℂ) (a q B : ℕ) (s : State)
    (hB : a*q+a+q+11 ≤ B) (hpc : s.pc = 0) (hb : WordBound B s) :
    BoundedRuns program n x B s 2 (initialized s) := by
  have h1 := writeNat_bound B s 2 1 hb (by omega) (by omega)
  have h2 := writeNat_bound B (writeNat s 2 1) 3 0 h1
    (by simp [writeNat,next,hpc]; omega) (by omega)
  refine .next (u := writeNat s 2 1) hb ?_ (.next h1 ?_ (.refl h2))
  all_goals simp [step,program,initialized,writeNat,next,hpc]

/-- The literal inverse scan has bounded, charged execution and preserves all
scalars, heaps, outputs and previous root requests. Entry registers are explicit. -/
theorem inverse_bounded (n : ℕ) (x : Fin n → ℂ) (a q B : ℕ) (s : State)
    (hq : 1 < q) (hc : Nat.Coprime a q) (hB : a*q+a+q+11 ≤ B)
    (hpc : s.pc = 0) (ha : s.natReg 0 = a) (hq' : s.natReg 1 = q)
    (hb : WordBound B s) : ∃ u : State,
    BoundedExecution program n x B s ((scan a q).steps+2) u ∧
      u.natReg 3 = ((a : ZMod q)⁻¹).val ∧ (scan a q).steps+2 ≤ 7*q+8 ∧ Frame s u := by
  have hstart := startup_bounded n x a q B s hB hpc hb
  have hctx : Context a q 0 (initialized s) := by
    simp [Context,initialized,writeNat,next,hpc,ha,hq']
  obtain ⟨u,hu,hdigit,hframe⟩ := loop_execution n x a q q 0 (initialized s) (by omega) (by omega) hctx
  have hcount : Counters a q (initialized s) := by
    simp [Counters,initialized,writeNat,next,hpc,ha,hq']
  have hbloop := hu.bounded_of_invariant (Interior a q B) ⟨hstart.final_bound,hcount⟩
    (fun _ h => h.1) (fun s u h => step_interior n x a q B s u (by omega) hB h)
  refine ⟨u,?_,?_,?_,?_⟩
  · convert hstart.executes hbloop using 1; simp [scan]; omega
  · exact hdigit.trans (scan_correct a q hq hc)
  · have h := scanLoop_cost a q q 0; change (scanLoop a q q 0).steps+2 ≤ 7*q+8; omega
  · simpa [Frame,initialized,writeNat,next] using hframe


theorem crtDigit_eq (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hc : Pairwise (fun i j => Nat.Coprime (r i) (r j))) (i : ι) :
    crtDigit r i = UniformCRT.inverseDigit r i := by
  unfold crtDigit
  split_ifs with h1
  · have hd := UniformCRT.inverseDigit_lt r i (hr i); omega
  · exact scan_correct _ _ (by have h := hr i; omega) (UniformCRT.cofactor_coprime r hc i)

/-- Concrete CRT cofactors fit the working length; their candidate products
are at most that length, not an unbounded integer multiplication. -/
theorem cofactor_budget (r : ι → ℕ) (hr : ∀ i, 0 < r i) (i : ι) :
    UniformCRT.cofactor r i * r i + UniformCRT.cofactor r i + r i + 11 ≤
      3*(∏ j,r j)+11 := by
  have he := UniformCRT.cofactor_mul r i
  have hco : 0 < UniformCRT.cofactor r i := Finset.prod_pos (fun j _ => hr j)
  have hq : 1 ≤ r i := hr i
  have h1 := Nat.mul_le_mul_left (UniformCRT.cofactor r i) hq
  have h2 := Nat.mul_le_mul_right (r i) hco
  simp only [Nat.mul_one,Nat.one_mul] at h1 h2
  omega

/-- Every nontrivial factor's scanned digit is the precise existing CRT digit,
with a bounded instruction trace preserving a previously supplied master root. -/
theorem crt_inverse_bounded (n : ℕ) (x : Fin n → ℂ) (r : ι → ℕ)
    (hr : ∀ i, 0 < r i) (hc : Pairwise (fun i j => Nat.Coprime (r i) (r j)))
    (i : ι) (hi : 1 < r i) (B : ℕ) (s : State) (hB : 3*(∏ j,r j)+11 ≤ B)
    (hpc : s.pc = 0) (ha : s.natReg 0 = UniformCRT.cofactor r i)
    (hq : s.natReg 1 = r i) (hb : WordBound B s) : ∃ u : State,
    BoundedExecution program n x B s ((scan (UniformCRT.cofactor r i) (r i)).steps+2) u ∧
      u.natReg 3 = UniformCRT.inverseDigit r i ∧
      (scan (UniformCRT.cofactor r i) (r i)).steps+2 ≤ 7*r i+8 ∧ Frame s u :=
  inverse_bounded n x _ _ B s hi (UniformCRT.cofactor_coprime r hc i)
    ((cofactor_budget r hr i).trans hB) hpc ha hq hb

end
end ExactFourierCircuits.UniformCRTMachine

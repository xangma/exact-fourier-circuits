import UniformAsymptotics

/- Counted functional integer loops. These are not a lowering to a fixed RAM program.
   Counts charge integer arithmetic, comparisons, state assignments and control transfers.
   No primality oracle or `Nat.find` is executed by the preparation functions. -/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformWorkingPreparation
open Filter Asymptotics

structure Counted (α : Type) where
  value : α
  cost : ℕ
  deriving Repr

/-- Zero fuel: guard and return. Nonzero: guard, decrement, modulo, comparison;
    rejection returns, continuation also increments divisor and transfers control. -/
def trialLoop (p d : ℕ) : ℕ → Counted Bool
  | 0 => ⟨true, 2⟩
  | f + 1 =>
    if p % d = 0 then ⟨false, 5⟩ else
      let tail := trialLoop p (d + 1) f
      ⟨tail.value, tail.cost + 7⟩

def trialPrime (p : ℕ) : Counted Bool :=
  if p < 2 then ⟨false, 2⟩ else
    let ans := trialLoop p 2 (p - 2)
    ⟨ans.value, ans.cost + 3⟩

theorem trialLoop_true (p d f : ℕ) : (trialLoop p d f).value = true ↔
    ∀ q, d ≤ q → q < d + f → p % q ≠ 0 := by
  induction f generalizing d with
  | zero =>
    simp only [trialLoop]
    constructor
    · intro _ q hd hq; omega
    · intro _; trivial
  | succ f ih =>
    by_cases hz : p % d = 0
    · simp only [trialLoop, hz, ite_true]
      constructor
      · intro h; contradiction
      · intro h
        exact (h d le_rfl (by omega) hz).elim
    · simp only [trialLoop, hz, ite_false]
      rw [ih]
      constructor
      · intro h q hd hq
        by_cases he : q = d
        · simpa only [he] using hz
        · exact h q (by omega) (by omega)
      · intro h q hd hq
        exact h q (by omega) (by omega)

theorem trialPrime_true (p : ℕ) : (trialPrime p).value = true ↔ Nat.Prime p := by
  by_cases hp : p < 2
  · simp only [trialPrime, hp, ite_true]
    exact ⟨fun h => by contradiction, fun h => by have h2 := h.two_le; omega⟩
  · simp only [trialPrime, hp, ite_false]
    rw [trialLoop_true, Nat.prime_def_lt']
    have h2 : 2 ≤ p := by omega
    constructor
    · intro h
      refine ⟨h2, ?_⟩
      intro q hq hqp hdiv
      exact h q hq (by omega) (Nat.mod_eq_zero_of_dvd hdiv)
    · intro h q hq hqp hz
      exact h.2 q hq (by omega) (Nat.dvd_of_mod_eq_zero hz)

theorem trialLoop_cost (p d f : ℕ) : (trialLoop p d f).cost ≤ 7 * f + 2 := by
  induction f generalizing d with
  | zero => simp [trialLoop]
  | succ f ih =>
    by_cases hz : p % d = 0
    · simp [trialLoop, hz]; omega
    · simp only [trialLoop, hz, ite_false]
      have h := ih (d + 1)
      omega

theorem trialPrime_cost (p : ℕ) : (trialPrime p).cost ≤ 7 * p + 5 := by
  by_cases hp : p < 2
  · simp [trialPrime, hp]
  · simp only [trialPrime, hp, ite_false]
    have h := trialLoop_cost p 2 (p - 2)
    omega

structure Prefix where
  axes : ℕ
  product : ℕ
  next : ℕ
  deriving Repr, DecidableEq

/-- Candidate scan. The increments, product test and updates are explicitly charged.
    Fuel is only a termination guard; a successful run stops at the first excess product. -/
def selectLoop (n p j R : ℕ) : ℕ → Counted (Option Prefix)
  | 0 => ⟨none, 2⟩
  | f + 1 =>
    let check := trialPrime p
    if check.value = true then
      let newR := R * p
      if 2 * n < newR then ⟨some ⟨j, R, p⟩, check.cost + 12⟩ else
        let tail := selectLoop n (p + 1) (j + 1) newR f
        ⟨tail.value, tail.cost + check.cost + 12⟩
    else
      let tail := selectLoop n (p + 1) j R f
      ⟨tail.value, tail.cost + check.cost + 8⟩

def candidateLimit (n : ℕ) : ℕ := 64 * (2 * n + 2) ^ 2 + 1
def selectPrefix (n : ℕ) : Counted (Option Prefix) :=
  let ans := selectLoop n 3 0 1 (candidateLimit n)
  ⟨ans.value, ans.cost + 12⟩

theorem counting_succ (p : ℕ) : Nat.primeCounting' (p + 1) = Nat.primeCounting' p +
    (if Nat.Prime p then 1 else 0) := Nat.count_succ _ _

theorem prime_of_count {p j : ℕ} (hp : Nat.Prime p) (hc : Nat.primeCounting' p = j + 1) :
    p = UniformWorkingLength.oddPrime j := by
  rw [UniformWorkingLength.oddPrime_eq_nth]
  have h := Nat.nth_count hp
  change Nat.nth Nat.Prime (Nat.primeCounting' p) = p at h
  rw [hc] at h
  exact h.symm

theorem advance_cost_bound (p q tail check extra : ℕ) (hp : p < q)
    (ht : tail ≤ (q - (p + 1) + 1) * (7 * q + 17) + 2)
    (hc : check ≤ 7 * p + 5) (he : extra ≤ 12) :
    tail + check + extra ≤ (q - p + 1) * (7 * q + 17) + 2 := by
  have hd : q - p + 1 = (q - (p + 1) + 1) + 1 := by omega
  calc
    tail + check + extra ≤ ((q - (p + 1) + 1) * (7 * q + 17) + 2) + (7 * p + 5) + 12 := by omega
    _ ≤ (q - (p + 1) + 1) * (7 * q + 17) + (7 * q + 17) + 2 := by omega
    _ = (q - p + 1) * (7 * q + 17) + 2 := by rw [hd]; ring

theorem selectLoop_spec (n : ℕ) (hn : 0 < n) (p j f : ℕ)
    (h3 : 3 ≤ p) (hp : p ≤ UniformWorkingLength.nextPrime n)
    (hc : Nat.primeCounting' p = j + 1)
    (hf : UniformWorkingLength.nextPrime n - p + 1 ≤ f) :
    (selectLoop n p j (UniformWorkingLength.primeProduct j) f).value =
      some ⟨UniformWorkingLength.axisCount n, UniformWorkingLength.oddProduct n, UniformWorkingLength.nextPrime n⟩ ∧
    (selectLoop n p j (UniformWorkingLength.primeProduct j) f).cost ≤
      (UniformWorkingLength.nextPrime n - p + 1) * (7 * UniformWorkingLength.nextPrime n + 17) + 2 := by
  induction f generalizing p j with
  | zero => omega
  | succ f ih =>
    by_cases he : p = UniformWorkingLength.nextPrime n
    · have hpr : Nat.Prime p := he ▸ UniformWorkingLength.oddPrime_prime _
      have hcheck := (trialPrime_true p).2 hpr
      have hj : j = UniformWorkingLength.axisCount n := by
        have hq := UniformWorkingLength.oddPrime_count (UniformWorkingLength.axisCount n)
        change Nat.primeCounting' (UniformWorkingLength.nextPrime n) = _ at hq
        rw [he] at hc
        omega
      have hprod : 2 * n < UniformWorkingLength.primeProduct j * p := by
        simpa only [hj, he, UniformWorkingLength.oddProduct] using (UniformWorkingLength.maximal_product hn).2
      simp only [selectLoop, hcheck, ite_true, hprod]
      constructor
      · simp only [hj, he]; rfl
      · have hcost := trialPrime_cost p
        rw [he] at hcost ⊢
        simp only [Nat.sub_self, Nat.zero_add, Nat.one_mul]
        omega
    · have hlt : p < UniformWorkingLength.nextPrime n := by omega
      by_cases hpr : Nat.Prime p
      · have hcheck := (trialPrime_true p).2 hpr
        have hjp := prime_of_count hpr hc
        have hj : j < UniformWorkingLength.axisCount n := by
          by_contra h
          have hq := UniformWorkingLength.oddPrime_strictMono.monotone
            (show UniformWorkingLength.axisCount n ≤ j by omega)
          rw [← hjp] at hq
          change UniformWorkingLength.nextPrime n ≤ p at hq
          omega
        have hnew : UniformWorkingLength.primeProduct j * p = UniformWorkingLength.primeProduct (j + 1) := by
          rw [hjp, UniformWorkingLength.primeProduct]
        have hnprod : UniformWorkingLength.primeProduct (j + 1) ≤ 2 * n :=
          (UniformWorkingLength.primeProduct_strictMono.monotone (by omega)).trans (UniformWorkingLength.maximal_product hn).1
        have hnot : ¬2 * n < UniformWorkingLength.primeProduct (j + 1) := by omega
        have hc' : Nat.primeCounting' (p + 1) = (j + 1) + 1 := by simp only [counting_succ, hpr, ite_true, hc]
        have ht := ih (p + 1) (j + 1) (by omega) (by omega) hc' (by omega)
        simp only [selectLoop, hcheck, ite_true, hnew, hnot, ite_false]
        constructor
        · exact ht.1
        · exact advance_cost_bound _ _ _ _ _ hlt ht.2 (trialPrime_cost p) (by omega)
      · have hcheck : (trialPrime p).value ≠ true := (trialPrime_true p).not.mpr hpr
        have hc' : Nat.primeCounting' (p + 1) = j + 1 := by simp only [counting_succ, hpr, ite_false, hc, Nat.add_zero]
        have ht := ih (p + 1) j (by omega) (by omega) hc' (by omega)
        simp only [selectLoop, hcheck]
        constructor
        · exact ht.1
        · exact advance_cost_bound _ _ _ _ _ hlt ht.2 (trialPrime_cost p) (by omega)

theorem selectPrefix_spec {n : ℕ} (hn : 0 < n) :
    (selectPrefix n).value = some ⟨UniformWorkingLength.axisCount n,
      UniformWorkingLength.oddProduct n, UniformWorkingLength.nextPrime n⟩ ∧
    (selectPrefix n).cost ≤ UniformWorkingLength.nextPrime n * (7 * UniformWorkingLength.nextPrime n + 17) + 14 := by
  have hj : UniformWorkingLength.axisCount n ≤ 2 * n := by
    have h := UniformWorkingLength.firstExceed_bound n
    unfold UniformWorkingLength.axisCount
    omega
  have hq : UniformWorkingLength.nextPrime n ≤ candidateLimit n := by
    have h := UniformWorkingLength.nextPrime_upper n
    have hm := Nat.pow_le_pow_left (Nat.add_le_add_right hj 2) 2
    unfold candidateLimit
    exact h.trans ((Nat.mul_le_mul_left 64 hm).trans (Nat.le_add_right _ 1))
  have hq3 : 3 ≤ UniformWorkingLength.nextPrime n := by
    have hp := UniformWorkingLength.oddPrime_lower (UniformWorkingLength.axisCount n)
    change UniformWorkingLength.axisCount n + 3 ≤ UniformWorkingLength.nextPrime n at hp
    omega
  have h := selectLoop_spec n hn 3 0 (candidateLimit n) (by omega) hq3
    (by norm_num [Nat.primeCounting', Nat.count_succ]) (by omega)
  have hinit : UniformWorkingLength.primeProduct 0 = 1 := rfl
  rw [hinit] at h
  constructor
  · exact h.1
  · have hm := Nat.mul_le_mul_right (7 * UniformWorkingLength.nextPrime n + 17)
      (show UniformWorkingLength.nextPrime n - 3 + 1 ≤ UniformWorkingLength.nextPrime n by omega)
    have hcost := h.2
    change (selectLoop n 3 0 1 (candidateLimit n)).cost + 12 ≤ _
    omega

theorem selectPrefix_cost_polynomial {n : ℕ} (hn : 0 < n) :
    (selectPrefix n).cost ≤ 30000 * (UniformWorkingLength.axisCount n + 2) ^ 4 := by
  have hc := (selectPrefix_spec hn).2
  have hq := UniformWorkingLength.nextPrime_upper n
  have hpow := Nat.pow_le_pow_left hq 2
  have ha : 4 ≤ (UniformWorkingLength.axisCount n + 2) ^ 2 := by
    have h := Nat.pow_le_pow_left (show 2 ≤ UniformWorkingLength.axisCount n + 2 by omega) 2
    exact h
  have hb : UniformWorkingLength.nextPrime n * (7 * UniformWorkingLength.nextPrime n + 17) + 14 ≤
      30000 * ((UniformWorkingLength.axisCount n + 2) ^ 2) ^ 2 := by nlinarith
  simpa only [← pow_mul, Nat.reduceMul] using hc.trans hb

structure Doubling where
  exponent : ℕ
  binary : ℕ
  length : ℕ
  deriving Repr, DecidableEq

/-- Each continuation charges the guard, fuel decrement, comparison, two doublings,
    exponent increment, state assignments and control transfer. -/
def doubleLoop (n e B L : ℕ) : ℕ → Counted (Option Doubling)
  | 0 => ⟨none, 2⟩
  | f + 1 =>
    if 2 * n ≤ L then ⟨some ⟨e, B, L⟩, 5⟩ else
      let tail := doubleLoop n (e + 1) (2 * B) (2 * L) f
      ⟨tail.value, tail.cost + 10⟩

theorem doublingExponent_bound (n : ℕ) : UniformWorkingLength.doublingExponent n ≤ 2 * n := by
  apply Nat.find_min' (UniformWorkingLength.doubling_exists n)
  have hpow := (Nat.lt_pow_self (by norm_num : 1 < 2) (n := 2 * n)).le
  have hR := UniformWorkingLength.oddProduct_pos n
  nlinarith

theorem doubleLoop_spec (n e f : ℕ) (he : e ≤ UniformWorkingLength.doublingExponent n)
    (hf : UniformWorkingLength.doublingExponent n - e + 1 ≤ f) :
    (doubleLoop n e (2 ^ e) (UniformWorkingLength.oddProduct n * 2 ^ e) f).value =
      some ⟨UniformWorkingLength.doublingExponent n, UniformWorkingLength.binaryFactor n,
        UniformWorkingLength.workingLength n⟩ ∧
    (doubleLoop n e (2 ^ e) (UniformWorkingLength.oddProduct n * 2 ^ e) f).cost ≤
      10 * (UniformWorkingLength.doublingExponent n - e + 1) + 5 := by
  induction f generalizing e with
  | zero => omega
  | succ f ih =>
    by_cases heq : e = UniformWorkingLength.doublingExponent n
    · have hstop : 2 * n ≤ UniformWorkingLength.oddProduct n * 2 ^ e := by
        simpa only [heq, UniformWorkingLength.workingLength, UniformWorkingLength.binaryFactor]
          using UniformWorkingLength.workingLength_lower n
      simp only [doubleLoop, hstop, ite_true]
      constructor
      · simp only [heq, UniformWorkingLength.binaryFactor, UniformWorkingLength.workingLength]
      · omega
    · have hlt : e < UniformWorkingLength.doublingExponent n := by omega
      have hstop : ¬2 * n ≤ UniformWorkingLength.oddProduct n * 2 ^ e :=
        Nat.not_le.mpr (UniformWorkingLength.doubling_minimal n e hlt)
      have ht := ih (e + 1) (by omega) (by omega)
      have hB : 2 * 2 ^ e = 2 ^ (e + 1) := by rw [pow_succ]; omega
      have hL : 2 * (UniformWorkingLength.oddProduct n * 2 ^ e) =
          UniformWorkingLength.oddProduct n * 2 ^ (e + 1) := by rw [pow_succ]; ring
      simp only [doubleLoop, hstop, ite_false, hB, hL]
      exact ⟨ht.1, by have hc := ht.2; omega⟩

structure Prepared where
  axes : ℕ
  product : ℕ
  next : ℕ
  exponent : ℕ
  binary : ℕ
  length : ℕ
  deriving Repr, DecidableEq

/-- Actual preparation: trial division, successive candidates, then repeated doubling.
    The conservative twelve-unit headers charge the fixed arithmetic and state setup. -/
def prepare (n : ℕ) : Counted (Option Prepared) :=
  let selected := selectPrefix n
  match selected.value with
  | none => ⟨none, selected.cost + 2⟩
  | some p =>
    let doubled := doubleLoop n 0 1 p.product (2 * n + 1)
    match doubled.value with
    | none => ⟨none, selected.cost + doubled.cost + 12⟩
    | some d => ⟨some ⟨p.axes, p.product, p.next, d.exponent, d.binary, d.length⟩,
        selected.cost + doubled.cost + 12⟩

theorem prepare_spec {n : ℕ} (hn : 0 < n) :
    (prepare n).value = some ⟨UniformWorkingLength.axisCount n,
      UniformWorkingLength.oddProduct n, UniformWorkingLength.nextPrime n,
      UniformWorkingLength.doublingExponent n, UniformWorkingLength.binaryFactor n,
      UniformWorkingLength.workingLength n⟩ ∧
    (prepare n).cost ≤ (selectPrefix n).cost +
      10 * (UniformWorkingLength.doublingExponent n + 1) + 17 := by
  have hp := (selectPrefix_spec hn).1
  have hd := doubleLoop_spec n 0 (2 * n + 1) (by omega)
    (by have h := doublingExponent_bound n; omega)
  simp only [Nat.sub_zero, pow_zero, Nat.mul_one] at hd
  simp only [prepare, hp, hd.1]
  exact ⟨trivial, by have hc := hd.2; omega⟩

theorem prepare_cost_polynomial {n : ℕ} (hn : 0 < n) :
    (prepare n).cost ≤ 40000 * (UniformWorkingLength.axisCount n + 2) ^ 4 := by
  have hc := (prepare_spec hn).2
  have hp := selectPrefix_cost_polynomial hn
  have he : UniformWorkingLength.doublingExponent n < UniformWorkingLength.binaryFactor n :=
    Nat.lt_pow_self (by norm_num : 1 < 2)
  have hb := UniformWorkingLength.binaryFactor_quadratic hn
  have ha : 4 ≤ (UniformWorkingLength.axisCount n + 2) ^ 2 :=
    Nat.pow_le_pow_left (show 2 ≤ UniformWorkingLength.axisCount n + 2 by omega) 2
  have hs : (UniformWorkingLength.axisCount n + 2) ^ 4 =
      ((UniformWorkingLength.axisCount n + 2) ^ 2) ^ 2 := by rw [← pow_mul]
  rw [hs] at hp ⊢
  nlinarith

/-- The polynomial bound concerns the charged functional loops above, not an oracle. -/
theorem preparation_isBigO_axisPolynomial :
    (fun n : ℕ => ((prepare n).cost : ℝ)) =O[atTop]
      (fun n : ℕ => ((UniformWorkingLength.axisCount n + 2 : ℕ) : ℝ) ^ 4) := by
  apply IsBigO.of_bound 40000
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hc : ((prepare n).cost : ℝ) ≤
      40000 * ((UniformWorkingLength.axisCount n + 2 : ℕ) : ℝ) ^ 4 := by
    exact_mod_cast prepare_cost_polynomial (show 0 < n by omega)
  simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (by positivity : 0 ≤ ((UniformWorkingLength.axisCount n + 2 : ℕ) : ℝ) ^ 4)] using hc

theorem axisCount_plus_two_isBigO_log :
    (fun n : ℕ => ((UniformWorkingLength.axisCount n + 2 : ℕ) : ℝ)) =O[atTop]
      (fun n : ℕ => Real.log (n : ℝ)) := by
  have hadd : (fun n : ℕ => ((UniformWorkingLength.axisCount n + 2 : ℕ) : ℝ)) =O[atTop]
      (fun n : ℕ => ((UniformWorkingLength.axisCount n + 1 : ℕ) : ℝ)) := by
    apply IsBigO.of_bound 2
    filter_upwards [] with n
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
    push_cast
    linarith [show (0 : ℝ) ≤ UniformWorkingLength.axisCount n by positivity]
  have htlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htloglog : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp htlog
  have hratio : (fun n : ℕ => Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) =O[atTop]
      (fun n : ℕ => Real.log (n : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards [htlog.eventually (eventually_ge_atTop 1),
      htloglog.eventually (eventually_ge_atTop 1)] with n hlog hloglog
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by linarith), one_mul]
    apply (div_le_iff₀ (by linarith)).2
    nlinarith
  exact hadd.trans (UniformAsymptotics.axisCount_isBigO.trans hratio)

theorem preparation_isBigO_log_four :
    (fun n : ℕ => ((prepare n).cost : ℝ)) =O[atTop]
      (fun n : ℕ => Real.log (n : ℝ) ^ 4) :=
  preparation_isBigO_axisPolynomial.trans (axisCount_plus_two_isBigO_log.pow 4)

/-- Unconditional sublinear charged preparation for the actual selected working length.
    This does not assert the existence of the fixed-program RAM implementation. -/
theorem preparation_isLittleO_input :
    (fun n : ℕ => ((prepare n).cost : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  have hlog : (fun n : ℕ => Real.log (n : ℝ) ^ 4) =o[atTop] (fun n : ℕ => (n : ℝ)) :=
    Real.isLittleO_pow_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  exact preparation_isBigO_log_four.trans_isLittleO hlog

end ExactFourierCircuits.UniformWorkingPreparation

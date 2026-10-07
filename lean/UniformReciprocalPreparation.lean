import UniformNewton

/-! A shared reciprocal-series coefficient bank. The syntax extends its supplied
coefficient program once. Its only new division has denominator `h₀`; every
other new node is a field addition, subtraction or multiplication. -/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformReciprocalPreparation
open scoped BigOperators
open UniformScalarPreparation

noncomputable section

theorem inverse_coeff_succ (f : PowerSeries ℂ) (k : ℕ) :
    PowerSeries.coeff (k + 1) f⁻¹ =
      -(PowerSeries.constantCoeff f)⁻¹ *
        ∑ j : Fin (k + 1), PowerSeries.coeff (j.val + 1) f *
          PowerSeries.coeff (k - j.val) f⁻¹ := by
  rw [PowerSeries.coeff_inv, ite_eq_right (by omega)]
  congr 1
  rw [Finset.Nat.sum_antidiagonal_succ]
  simp only [lt_self_iff_false, ↓reduceIte, zero_add]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Fin.sum_univ_eq_sum_range (fun j => PowerSeries.coeff (j + 1) f *
    PowerSeries.coeff (k - j) f⁻¹) (k + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [show k - j < k + 1 by omega, ↓reduceIte]

/-- References to the supplied h-bank and the already prepared g-bank. -/
structure Bank (r n k : ℕ) where
  length : ℕ
  program : Program r length
  h : Fin (n + 1) → Fin length
  g : Fin (k + 1) → Fin length
  zero : Fin length
  inverse : Fin length

namespace Bank

def push {r n k : ℕ} (b : Bank r n k) (i : Instruction r b.length) : Bank r n k where
  length := b.length + 1
  program := .step b.program i
  h := fun j => (b.h j).castSucc
  g := fun j => (b.g j).castSucc
  zero := b.zero.castSucc
  inverse := b.inverse.castSucc

@[simp] theorem push_length {r n k : ℕ} (b : Bank r n k) (i : Instruction r b.length) :
    (b.push i).length = b.length + 1 := rfl

@[simp] theorem push_eval_old {r n k : ℕ} (b : Bank r n k)
    (i : Instruction r b.length) (roots : Fin r → ℂ) (j : Fin b.length) :
    (b.push i).program.eval roots j.castSucc = b.program.eval roots j := by
  simp [push]

@[simp] theorem push_eval_last {r n k : ℕ} (b : Bank r n k)
    (i : Instruction r b.length) (roots : Fin r → ℂ) :
    (b.push i).program.eval roots (Fin.last b.length) =
      i.eval roots (b.program.eval roots) := by
  simp [push]

def Correct {r n k : ℕ} (b : Bank r n k) (roots : Fin r → ℂ)
    (f : PowerSeries ℂ) : Prop :=
  (∀ j, b.program.eval roots (b.h j) = PowerSeries.coeff j.val f) ∧
  (∀ j, b.program.eval roots (b.g j) = PowerSeries.coeff j.val f⁻¹) ∧
  b.program.eval roots b.zero = 0 ∧
  b.program.eval roots b.inverse = (PowerSeries.constantCoeff f)⁻¹

theorem correct_push {r n k : ℕ} (b : Bank r n k) (i : Instruction r b.length)
    (roots : Fin r → ℂ) (f : PowerSeries ℂ) (hb : b.Correct roots f) :
    (b.push i).Correct roots f := by
  rcases hb with ⟨hh, hg, hz, hi⟩
  exact ⟨fun j => by simpa [push] using hh j,
    fun j => by simpa [push] using hg j,
    by simpa [push] using hz, by simpa [push] using hi⟩

end Bank

structure SumBank (r n k : ℕ) where
  bank : Bank r n k
  acc : Fin bank.length

namespace SumBank

/-- Two shared nodes add one h_j g_(degree-j) product to the accumulator. -/
def term {r n k : ℕ} (s : SumBank r n k) (hk : k < n)
    (j : Fin (k + 1)) : SumBank r n k :=
  let p := s.bank.push (.mul (s.bank.h ⟨j.val + 1, by omega⟩)
    (s.bank.g ⟨k - j.val, by omega⟩))
  let q := p.push (.add s.acc.castSucc (Fin.last s.bank.length))
  ⟨q, Fin.last p.length⟩

@[simp] theorem term_length {r n k : ℕ} (s : SumBank r n k) (hk : k < n)
    (j : Fin (k + 1)) : (s.term hk j).bank.length = s.bank.length + 2 := by
  change s.bank.length + 1 + 1 = s.bank.length + 2
  omega

theorem term_correct {r n k : ℕ} (s : SumBank r n k) (hk : k < n)
    (j : Fin (k + 1)) (roots : Fin r → ℂ) (f : PowerSeries ℂ)
    (hs : s.bank.Correct roots f) : (s.term hk j).bank.Correct roots f :=
  Bank.correct_push _ _ _ _ (Bank.correct_push _ _ _ _ hs)

theorem term_acc {r n k : ℕ} (s : SumBank r n k) (hk : k < n)
    (j : Fin (k + 1)) (roots : Fin r → ℂ) (f : PowerSeries ℂ)
    (hs : s.bank.Correct roots f) :
    (s.term hk j).bank.program.eval roots (s.term hk j).acc =
      s.bank.program.eval roots s.acc + PowerSeries.coeff (j.val + 1) f *
        PowerSeries.coeff (k - j.val) f⁻¹ := by
  simp only [term, Bank.push_eval_last, Instruction.eval, Bank.push_eval_old]
  rw [hs.1, hs.2.1]

theorem term_admissible {r n k : ℕ} (s : SumBank r n k) (hk : k < n)
    (j : Fin (k + 1)) (roots : Fin r → ℂ) (hs : s.bank.program.Admissible roots) :
    (s.term hk j).bank.program.Admissible roots := by
  simpa [term, Bank.push, Program.Admissible, Instruction.Admissible] using hs

def terms {r n k : ℕ} (s : SumBank r n k) (hk : k < n) :
    List (Fin (k + 1)) → SumBank r n k
  | [] => s
  | j :: js => terms (s.term hk j) hk js

theorem terms_length {r n k : ℕ} (s : SumBank r n k) (hk : k < n)
    (js : List (Fin (k + 1))) :
    (s.terms hk js).bank.length = s.bank.length + 2 * js.length := by
  induction js generalizing s with
  | nil => simp [terms]
  | cons j js ih => simp only [terms, ih, term_length, List.length_cons]; omega

theorem terms_correct {r n k : ℕ} (s : SumBank r n k) (hk : k < n)
    (js : List (Fin (k + 1))) (roots : Fin r → ℂ) (f : PowerSeries ℂ)
    (hs : s.bank.Correct roots f) : (s.terms hk js).bank.Correct roots f := by
  induction js generalizing s with
  | nil => exact hs
  | cons j js ih => exact ih _ (s.term_correct hk j roots f hs)

theorem terms_acc {r n k : ℕ} (s : SumBank r n k) (hk : k < n)
    (js : List (Fin (k + 1))) (roots : Fin r → ℂ) (f : PowerSeries ℂ)
    (hs : s.bank.Correct roots f) :
    (s.terms hk js).bank.program.eval roots (s.terms hk js).acc =
      s.bank.program.eval roots s.acc +
        (js.map (fun j => PowerSeries.coeff (j.val + 1) f *
          PowerSeries.coeff (k - j.val) f⁻¹)).sum := by
  induction js generalizing s with
  | nil => simp [terms]
  | cons j js ih =>
    rw [terms, ih _ (s.term_correct hk j roots f hs), s.term_acc hk j roots f hs]
    simp [List.map_cons, List.sum_cons, add_assoc]

theorem terms_admissible {r n k : ℕ} (s : SumBank r n k) (hk : k < n)
    (js : List (Fin (k + 1))) (roots : Fin r → ℂ)
    (hs : s.bank.program.Admissible roots) :
    (s.terms hk js).bank.program.Admissible roots := by
  induction js generalizing s with
  | nil => exact hs
  | cons j js ih => exact ih _ (s.term_admissible hk j roots hs)

end SumBank

def initial {r n : ℕ} (d : DAG r (n + 1)) : Bank r n 0 :=
  let p := Program.step d.program (.rational 0)
  let q := Program.step p (.rational 1)
  let t := Program.step q (.divide (Fin.last (d.length + 1))
    ((d.output 0).castSucc.castSucc))
  { length := d.length + 3, program := t,
    h := fun j => (d.output j).castSucc.castSucc.castSucc,
    g := fun _ => Fin.last (d.length + 2),
    zero := (Fin.last d.length).castSucc.castSucc,
    inverse := Fin.last (d.length + 2) }

@[simp] theorem initial_length {r n : ℕ} (d : DAG r (n + 1)) :
    (initial d).length = d.length + 3 := rfl

theorem initial_correct {r n : ℕ} (d : DAG r (n + 1)) (roots : Fin r → ℂ)
    (f : PowerSeries ℂ)
    (hd : ∀ j, d.program.eval roots (d.output j) = PowerSeries.coeff j.val f) :
    (initial d).Correct roots f := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j; simpa [initial, Program.eval] using hd j
  · intro j
    have hj : j = 0 := Fin.ext (by omega)
    subst j
    simp [initial, Instruction.eval, hd, PowerSeries.coeff_inv]
  · simp [initial, Instruction.eval]
  · simp [initial, Instruction.eval, hd]

theorem initial_admissible {r n : ℕ} (d : DAG r (n + 1)) (roots : Fin r → ℂ)
    (hd : d.Admissible roots) (hzero : d.program.eval roots (d.output 0) ≠ 0) :
    (initial d).program.Admissible roots := by
  simpa [initial, Program.Admissible, Instruction.Admissible, Program.eval, DAG.Admissible]
    using And.intro hd hzero

/-- Degree k+1 uses the previously computed coefficients through degree k. -/
def next {r n k : ℕ} (b : Bank r n k) (hk : k < n) : Bank r n (k + 1) :=
  let s := (SumBank.mk b b.zero).terms hk (List.finRange (k + 1))
  let p := s.bank.push (.mul s.bank.inverse s.acc)
  let q := p.push (.sub p.zero (Fin.last s.bank.length))
  { length := q.length, program := q.program, h := q.h,
    g := Fin.snoc q.g (Fin.last p.length), zero := q.zero, inverse := q.inverse }

theorem next_length {r n k : ℕ} (b : Bank r n k) (hk : k < n) :
    (next b hk).length = b.length + 2 * (k + 1) + 2 := by
  change ((SumBank.mk b b.zero).terms hk (List.finRange (k + 1))).bank.length + 1 + 1 = _
  rw [SumBank.terms_length]
  simp only [List.length_finRange]

theorem next_correct {r n k : ℕ} (b : Bank r n k) (hk : k < n)
    (roots : Fin r → ℂ) (f : PowerSeries ℂ) (hb : b.Correct roots f) :
    (next b hk).Correct roots f := by
  let s := (SumBank.mk b b.zero).terms hk (List.finRange (k + 1))
  have hs : s.bank.Correct roots f := SumBank.terms_correct _ _ _ _ _ hb
  have hacc : s.bank.program.eval roots s.acc =
      ∑ j : Fin (k + 1), PowerSeries.coeff (j.val + 1) f *
        PowerSeries.coeff (k - j.val) f⁻¹ := by
    have h := SumBank.terms_acc (SumBank.mk b b.zero) hk
      (List.finRange (k + 1)) roots f hb
    simpa only [hb.2.2.1, zero_add, ← List.ofFn_eq_map, List.sum_ofFn] using h
  let p := s.bank.push (.mul s.bank.inverse s.acc)
  let q := p.push (.sub p.zero (Fin.last s.bank.length))
  have hq : q.Correct roots f :=
    Bank.correct_push _ _ _ _ (Bank.correct_push _ _ _ _ hs)
  refine ⟨hq.1, ?_, hq.2.2.1, hq.2.2.2⟩
  intro j
  change q.program.eval roots (Fin.snoc (α := fun _ => Fin q.length) q.g (Fin.last p.length) j) =
    PowerSeries.coeff j.val f⁻¹
  refine Fin.lastCases ?_ (fun j => ?_) j
  · dsimp only [q, p, Bank.push]
    simp only [Fin.snoc_last, Fin.val_last, Program.eval, Instruction.eval,
      Fin.snoc_castSucc]
    rw [hs.2.2.1, hs.2.2.2, hacc, inverse_coeff_succ]
    ring
  · simpa only [q, p, Bank.push, Fin.snoc_castSucc, Fin.val_castSucc] using hq.2.1 j

theorem next_admissible {r n k : ℕ} (b : Bank r n k) (hk : k < n)
    (roots : Fin r → ℂ) (hb : b.program.Admissible roots) :
    (next b hk).program.Admissible roots := by
  have hs := SumBank.terms_admissible (SumBank.mk b b.zero) hk
    (List.finRange (k + 1)) roots hb
  simpa [next, Bank.push, Program.Admissible, Instruction.Admissible] using hs

/-- The supplied program occurs once; recursion appends register instructions. -/
def build {r n : ℕ} (d : DAG r (n + 1)) : (k : ℕ) → k ≤ n → Bank r n k
  | 0, _ => initial d
  | k + 1, hk => next (build d k (by omega)) (by omega)

theorem build_length {r n : ℕ} (d : DAG r (n + 1)) (k : ℕ) (hk : k ≤ n) :
    (build d k hk).length = d.length + k * k + 3 * k + 3 := by
  induction k with
  | zero => simp [build]
  | succ k ih =>
    rw [build, next_length, ih]
    ring

theorem build_correct {r n : ℕ} (d : DAG r (n + 1)) (k : ℕ) (hk : k ≤ n)
    (roots : Fin r → ℂ) (f : PowerSeries ℂ)
    (hd : ∀ j, d.program.eval roots (d.output j) = PowerSeries.coeff j.val f) :
    (build d k hk).Correct roots f := by
  induction k with
  | zero => exact initial_correct d roots f hd
  | succ k ih => exact next_correct _ _ _ _ (ih (by omega))

theorem build_admissible {r n : ℕ} (d : DAG r (n + 1)) (k : ℕ) (hk : k ≤ n)
    (roots : Fin r → ℂ) (hd : d.Admissible roots)
    (hzero : d.program.eval roots (d.output 0) ≠ 0) :
    (build d k hk).program.Admissible roots := by
  induction k with
  | zero => exact initial_admissible d roots hd hzero
  | succ k ih => exact next_admissible _ _ _ (ih (by omega))

def reciprocal {r n : ℕ} (d : DAG r (n + 1)) : DAG r (n + 1) :=
  let b := build d n (le_refl n)
  ⟨b.length, b.program, b.g⟩

/-- Both banks reference the same extended program, without duplicated ancestry. -/
def shared {r n : ℕ} (d : DAG r (n + 1)) : DAG r ((n + 1) + (n + 1)) :=
  let b := build d n (le_refl n)
  ⟨b.length, b.program, Fin.addCases b.h b.g⟩

theorem reciprocal_length {r n : ℕ} (d : DAG r (n + 1)) :
    (reciprocal d).length = d.length + n * n + 3 * n + 3 := build_length d n _

theorem shared_length {r n : ℕ} (d : DAG r (n + 1)) :
    (shared d).length = d.length + n * n + 3 * n + 3 := build_length d n _

theorem reciprocal_admissible {r n : ℕ} (d : DAG r (n + 1)) (roots : Fin r → ℂ)
    (hd : d.Admissible roots) (hzero : d.program.eval roots (d.output 0) ≠ 0) :
    (reciprocal d).Admissible roots := build_admissible d n _ roots hd hzero

theorem shared_admissible {r n : ℕ} (d : DAG r (n + 1)) (roots : Fin r → ℂ)
    (hd : d.Admissible roots) (hzero : d.program.eval roots (d.output 0) ≠ 0) :
    (shared d).Admissible roots := build_admissible d n _ roots hd hzero

theorem reciprocal_run {r n : ℕ} (d : DAG r (n + 1)) (roots : Fin r → ℂ)
    (f : PowerSeries ℂ) (hd : d.Admissible roots)
    (hzero : d.program.eval roots (d.output 0) ≠ 0)
    (hcoeff : ∀ j, d.program.eval roots (d.output j) = PowerSeries.coeff j.val f)
    (j : Fin (n + 1)) :
    (reciprocal d).run roots (reciprocal_admissible d roots hd hzero) j =
      PowerSeries.coeff j.val f⁻¹ := (build_correct d n _ roots f hcoeff).2.1 j

theorem shared_run_h {r n : ℕ} (d : DAG r (n + 1)) (roots : Fin r → ℂ)
    (hd : d.Admissible roots) (hzero : d.program.eval roots (d.output 0) ≠ 0)
    (j : Fin (n + 1)) :
    (shared d).run roots (shared_admissible d roots hd hzero) (Fin.castAdd (n + 1) j) =
      d.run roots hd j := by
  let f : PowerSeries ℂ := PowerSeries.mk (fun k =>
    if hk : k < n + 1 then d.program.eval roots (d.output ⟨k, hk⟩) else 0)
  have hcoeff : ∀ j, d.program.eval roots (d.output j) = PowerSeries.coeff j.val f := by
    intro j; simp only [f, PowerSeries.coeff_mk, dite_eq_left j.isLt]
  simpa only [shared, DAG.run, Program.run, Fin.addCases_left, f, PowerSeries.coeff_mk,
    dite_eq_left j.isLt] using
    (build_correct d n _ roots f hcoeff).1 j

theorem shared_run_g {r n : ℕ} (d : DAG r (n + 1)) (roots : Fin r → ℂ)
    (hd : d.Admissible roots) (hzero : d.program.eval roots (d.output 0) ≠ 0)
    (j : Fin (n + 1)) :
    (shared d).run roots (shared_admissible d roots hd hzero) (Fin.natAdd (n + 1) j) =
      (reciprocal d).run roots (reciprocal_admissible d roots hd hzero) j := by
  simp only [shared, reciprocal, DAG.run, Program.run, Fin.addCases_right]

/-- The finite supplied h-bank is extended by zero for a canonical series. -/
def inputSeries {r n : ℕ} (d : DAG r (n + 1)) (roots : Fin r → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun k =>
    if hk : k < n + 1 then d.program.eval roots (d.output ⟨k, hk⟩) else 0)

@[simp] theorem inputSeries_coeff {r n : ℕ} (d : DAG r (n + 1))
    (roots : Fin r → ℂ) (j : Fin (n + 1)) :
    PowerSeries.coeff j.val (inputSeries d roots) = d.program.eval roots (d.output j) := by
  simp only [inputSeries, PowerSeries.coeff_mk, dite_eq_left j.isLt]

@[simp] theorem inputSeries_constant {r n : ℕ} (d : DAG r (n + 1))
    (roots : Fin r → ℂ) : PowerSeries.constantCoeff (inputSeries d roots) =
      d.program.eval roots (d.output 0) := by
  simpa only [Fin.val_zero, PowerSeries.coeff_zero_eq_constantCoeff] using inputSeries_coeff d roots 0

def values {r n : ℕ} (d : DAG r (n + 1)) (roots : Fin r → ℂ)
    (hd : d.Admissible roots) (hzero : d.program.eval roots (d.output 0) ≠ 0) :
    Fin (n + 1) → ℂ := (reciprocal d).run roots (reciprocal_admissible d roots hd hzero)

theorem values_eq_coeff_inverse {r n : ℕ} (d : DAG r (n + 1)) (roots : Fin r → ℂ)
    (hd : d.Admissible roots) (hzero : d.program.eval roots (d.output 0) ≠ 0)
    (j : Fin (n + 1)) :
    values d roots hd hzero j = PowerSeries.coeff j.val (inputSeries d roots)⁻¹ :=
  reciprocal_run d roots (inputSeries d roots) hd hzero
    (fun j => (inputSeries_coeff d roots j).symm) j

theorem values_zero {r n : ℕ} (d : DAG r (n + 1)) (roots : Fin r → ℂ)
    (hd : d.Admissible roots) (hzero : d.program.eval roots (d.output 0) ≠ 0) :
    values d roots hd hzero 0 = (d.run roots hd 0)⁻¹ := by
  rw [values_eq_coeff_inverse, PowerSeries.coeff_inv]
  simp [DAG.run, Program.run]

theorem values_succ {r n : ℕ} (d : DAG r (n + 1)) (roots : Fin r → ℂ)
    (hd : d.Admissible roots) (hzero : d.program.eval roots (d.output 0) ≠ 0)
    (k : Fin n) :
    values d roots hd hzero ⟨k.val + 1, by omega⟩ =
      -(d.run roots hd 0)⁻¹ * ∑ j : Fin (k.val + 1),
        d.run roots hd ⟨j.val + 1, by omega⟩ *
          values d roots hd hzero ⟨k.val - j.val, by omega⟩ := by
  rw [values_eq_coeff_inverse, inverse_coeff_succ, inputSeries_constant]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [values_eq_coeff_inverse]
  rw [inputSeries_coeff d roots ⟨j.val + 1, by omega⟩]
  rfl

theorem inverse_convolution (f : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f ≠ 0) (k : ℕ) :
    (∑ j : Fin (k + 1), PowerSeries.coeff j.val f *
      PowerSeries.coeff (k - j.val) f⁻¹) = if k = 0 then 1 else 0 := by
  have h := PowerSeries.coeff_mul k f f⁻¹
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  rw [Fin.sum_univ_eq_sum_range (fun j => PowerSeries.coeff j f *
    PowerSeries.coeff (k - j) f⁻¹) (k + 1)]
  simpa only [PowerSeries.mul_inv_cancel f hf, PowerSeries.coeff_one] using h.symm

/-- Every requested convolution coefficient is the Kronecker delta. -/
theorem values_convolution {r n : ℕ} (d : DAG r (n + 1)) (roots : Fin r → ℂ)
    (hd : d.Admissible roots) (hzero : d.program.eval roots (d.output 0) ≠ 0)
    (k : Fin (n + 1)) :
    (∑ j : Fin (k.val + 1), d.run roots hd ⟨j.val, by omega⟩ *
      values d roots hd hzero ⟨k.val - j.val, by omega⟩) =
        if k.val = 0 then 1 else 0 := by
  rw [← inverse_convolution (inputSeries d roots) (by simpa using hzero) k.val]
  apply Finset.sum_congr rfl
  intro j _
  rw [values_eq_coeff_inverse, inputSeries_coeff d roots ⟨j.val, by omega⟩]
  rfl

def preparedToeplitz {r n : ℕ} (d : DAG r (n + 1)) (roots : Fin r → ℂ)
    (hd : d.Admissible roots) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun i j =>
  if hij : j.val ≤ i.val then d.run roots hd ⟨i.val - j.val, by omega⟩ else 0

def preparedInverse {r n : ℕ} (d : DAG r (n + 1)) (roots : Fin r → ℂ)
    (hd : d.Admissible roots) (hzero : d.program.eval roots (d.output 0) ≠ 0) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun i j =>
  if hij : j.val ≤ i.val then values d roots hd hzero ⟨i.val - j.val, by omega⟩ else 0

theorem preparedToeplitz_eq {r n : ℕ} (d : DAG r (n + 1)) (roots : Fin r → ℂ)
    (hd : d.Admissible roots) : preparedToeplitz d roots hd =
      OAI.ExactFourier.CoefficientTime.truncMatrix (n + 1) (inputSeries d roots) := by
  ext i j
  by_cases hij : j.val ≤ i.val
  · simp only [preparedToeplitz, OAI.ExactFourier.CoefficientTime.truncMatrix,
      dite_eq_left hij, ite_eq_left hij]
    rw [inputSeries_coeff d roots ⟨i.val - j.val, by omega⟩]
    rfl
  · simp [preparedToeplitz, OAI.ExactFourier.CoefficientTime.truncMatrix, hij]

theorem preparedInverse_eq {r n : ℕ} (d : DAG r (n + 1)) (roots : Fin r → ℂ)
    (hd : d.Admissible roots) (hzero : d.program.eval roots (d.output 0) ≠ 0) :
    preparedInverse d roots hd hzero =
      OAI.ExactFourier.CoefficientTime.truncMatrix (n + 1) (inputSeries d roots)⁻¹ := by
  ext i j
  by_cases hij : j.val ≤ i.val
  · simp only [preparedInverse, OAI.ExactFourier.CoefficientTime.truncMatrix,
      dite_eq_left hij, ite_eq_left hij, values_eq_coeff_inverse]
  · simp [preparedInverse, OAI.ExactFourier.CoefficientTime.truncMatrix, hij]

theorem preparedInverse_is_inverse {r n : ℕ} (d : DAG r (n + 1))
    (roots : Fin r → ℂ) (hd : d.Admissible roots)
    (hzero : d.program.eval roots (d.output 0) ≠ 0) :
    preparedInverse d roots hd hzero = (preparedToeplitz d roots hd)⁻¹ := by
  rw [preparedInverse_eq, preparedToeplitz_eq,
    OAI.ExactFourier.ScalarConvolution.truncMatrix_inv _ _ (by simpa using hzero)]

theorem reciprocal_length_bound {r n : ℕ} (d : DAG r (n + 1)) :
    (reciprocal d).length ≤ d.length + 3 * (n + 1) ^ 2 := by
  rw [reciprocal_length]
  nlinarith

theorem reciprocal_output_bound {r n : ℕ} (d : DAG r (n + 1)) (j : Fin (n + 1)) :
    ((reciprocal d).output j).val < d.length + 3 * (n + 1) ^ 2 :=
  (reciprocal d).output j |>.isLt.trans_le (reciprocal_length_bound d)

def operandsBound {r k : ℕ} (i : Instruction r k) (B : ℕ) : Prop :=
  match i with
  | .add j l | .sub j l | .mul j l | .divide j l => j.val < B ∧ l.val < B
  | _ => True

theorem operandsBound_of_prior {r k : ℕ} (i : Instruction r k) {B : ℕ} (h : k ≤ B) :
    operandsBound i B := by
  cases i <;> simp only [operandsBound]
  all_goals first | trivial | exact ⟨Fin.isLt _ |>.trans_le h, Fin.isLt _ |>.trans_le h⟩

def referencesBound {r : ℕ} (B : ℕ) : {k : ℕ} → Program r k → Prop
  | 0, .nil => True
  | _ + 1, .step p i => referencesBound B p ∧ operandsBound i B

theorem referencesBound_of_length {r k B : ℕ} (p : Program r k) (h : k ≤ B) :
    referencesBound B p := by
  induction p with
  | nil => trivial
  | step p i ih => exact ⟨ih (by omega), operandsBound_of_prior i (by omega)⟩

/-- All internal register references, not only output addresses, are bounded. -/
theorem reciprocal_references_bound {r n : ℕ} (d : DAG r (n + 1)) :
    referencesBound (d.length + 3 * (n + 1) ^ 2) (reciprocal d).program :=
  referencesBound_of_length _ (reciprocal_length_bound d)

theorem preparedInverse_eq_of_coeff {r n : ℕ} (d : DAG r (n + 1))
    (roots : Fin r → ℂ) (hd : d.Admissible roots)
    (hzero : d.program.eval roots (d.output 0) ≠ 0) (f : PowerSeries ℂ)
    (hcoeff : ∀ j, d.program.eval roots (d.output j) = PowerSeries.coeff j.val f) :
    preparedInverse d roots hd hzero =
      OAI.ExactFourier.CoefficientTime.truncMatrix (n + 1) f⁻¹ := by
  ext i j
  by_cases hij : j.val ≤ i.val
  · simp only [preparedInverse, OAI.ExactFourier.CoefficientTime.truncMatrix,
      dite_eq_left hij, ite_eq_left hij]
    exact reciprocal_run d roots f hd hzero hcoeff ⟨i.val - j.val, by omega⟩
  · simp [preparedInverse, OAI.ExactFourier.CoefficientTime.truncMatrix, hij]

/-- Extract the existing Newton 1/H_j refs, without recompiling their ancestry. -/
def newtonInput (n : ℕ) : DAG 1 (n + 1) where
  length := UniformNewton.Preparation.inverseCount (n + 1) (n + 1)
  program := UniformNewton.Preparation.finalProgram (n + 1)
  output := UniformNewton.Preparation.finalInvH (n + 1)

theorem newtonInput_admissible {n : ℕ} {omega : ℂ}
    (hroot : IsPrimitiveRoot omega (n + 1)) :
    (newtonInput n).Admissible (UniformNewton.Preparation.roots omega) :=
  UniformNewton.Preparation.inverseProgram_admissible (by omega) hroot (n + 1) (le_refl _)

theorem newtonInput_coeff (n : ℕ) (omega : ℂ) (j : Fin (n + 1)) :
    (newtonInput n).program.eval (UniformNewton.Preparation.roots omega)
      ((newtonInput n).output j) =
        PowerSeries.coeff j.val (OAI.ExactFourier.NewtonFourier.invH omega) := by
  simpa only [newtonInput, OAI.ExactFourier.NewtonFourier.invH, PowerSeries.coeff_mk] using
    (UniformNewton.Preparation.finalProgram_values omega (n + 1) j).2.2.1

theorem newtonInput_zero (n : ℕ) (omega : ℂ) :
    (newtonInput n).program.eval (UniformNewton.Preparation.roots omega)
      ((newtonInput n).output 0) ≠ 0 := by
  rw [newtonInput_coeff]
  simp

def newtonReciprocal (n : ℕ) : DAG 1 (n + 1) := reciprocal (newtonInput n)

theorem newtonReciprocal_admissible {n : ℕ} {omega : ℂ}
    (hroot : IsPrimitiveRoot omega (n + 1)) :
    (newtonReciprocal n).Admissible (UniformNewton.Preparation.roots omega) :=
  reciprocal_admissible _ _ (newtonInput_admissible hroot) (newtonInput_zero n omega)

/-- These are coefficients of (invH omega)^-1, not coefficientwise 1/H_j. -/
theorem newtonReciprocal_run {n : ℕ} {omega : ℂ}
    (hroot : IsPrimitiveRoot omega (n + 1)) (j : Fin (n + 1)) :
    (newtonReciprocal n).run (UniformNewton.Preparation.roots omega)
      (newtonReciprocal_admissible hroot) j =
        PowerSeries.coeff j.val (OAI.ExactFourier.NewtonFourier.invH omega)⁻¹ :=
  reciprocal_run _ _ _ (newtonInput_admissible hroot) (newtonInput_zero n omega)
    (newtonInput_coeff n omega) j

theorem newtonReciprocal_length (n : ℕ) :
    (newtonReciprocal n).length = n * n + 11 * n + 14 := by
  rw [newtonReciprocal, reciprocal_length]
  change UniformNewton.Preparation.inverseCount (n + 1) (n + 1) +
    n * n + 3 * n + 3 = _
  rw [UniformNewton.Preparation.inverseCount_formula]
  ring

theorem newton_preparedInverse {n : ℕ} {omega : ℂ}
    (hroot : IsPrimitiveRoot omega (n + 1)) :
    preparedInverse (newtonInput n) (UniformNewton.Preparation.roots omega)
      (newtonInput_admissible hroot) (newtonInput_zero n omega) =
        (OAI.ExactFourier.CoefficientTime.truncMatrix (n + 1)
          (OAI.ExactFourier.NewtonFourier.invH omega))⁻¹ := by
  rw [preparedInverse_eq_of_coeff _ _ _ _ _ (newtonInput_coeff n omega),
    OAI.ExactFourier.ScalarConvolution.truncMatrix_inv _ _ (by simp)]

inductive CountKind where
  | root
  | divide
  | otherRational
  deriving DecidableEq

def instructionCount {r k : ℕ} (kind : CountKind) (i : Instruction r k) : ℕ :=
  match kind, i with
  | .root, .root _ => 1
  | .divide, .divide _ _ => 1
  | .otherRational, .rational q => if q = 0 ∨ q = 1 then 0 else 1
  | _, _ => 0

def programCount {r : ℕ} (kind : CountKind) : {k : ℕ} → Program r k → ℕ
  | 0, .nil => 0
  | _ + 1, .step p i => programCount kind p + instructionCount kind i

theorem initial_count {r n : ℕ} (kind : CountKind) (d : DAG r (n + 1)) :
    programCount kind (initial d).program = programCount kind d.program +
      if kind = .divide then 1 else 0 := by
  cases kind <;> simp [initial, programCount, instructionCount]

theorem term_count {r n k : ℕ} (kind : CountKind) (s : SumBank r n k)
    (hk : k < n) (j : Fin (k + 1)) :
    programCount kind (s.term hk j).bank.program = programCount kind s.bank.program := by
  cases kind <;> simp [SumBank.term, Bank.push, programCount, instructionCount]

theorem terms_count {r n k : ℕ} (kind : CountKind) (s : SumBank r n k)
    (hk : k < n) (js : List (Fin (k + 1))) :
    programCount kind (s.terms hk js).bank.program = programCount kind s.bank.program := by
  induction js generalizing s with
  | nil => rfl
  | cons j js ih => rw [SumBank.terms, ih, term_count]

theorem next_count {r n k : ℕ} (kind : CountKind) (b : Bank r n k) (hk : k < n) :
    programCount kind (next b hk).program = programCount kind b.program := by
  cases kind <;>
    simpa [next, Bank.push, programCount, instructionCount] using
      terms_count _ (SumBank.mk b b.zero) hk (List.finRange (k + 1))

theorem build_count {r n : ℕ} (kind : CountKind) (d : DAG r (n + 1))
    (k : ℕ) (hk : k ≤ n) :
    programCount kind (build d k hk).program = programCount kind d.program +
      if kind = .divide then 1 else 0 := by
  induction k with
  | zero => exact initial_count kind d
  | succ k ih => rw [build, next_count, ih]

theorem reciprocal_root_count {r n : ℕ} (d : DAG r (n + 1)) :
    programCount .root (reciprocal d).program = programCount .root d.program := by
  simpa only [reciprocal, ite_eq_right (by decide : CountKind.root ≠ .divide), add_zero] using
    build_count .root d n (le_refl n)

theorem reciprocal_divide_count {r n : ℕ} (d : DAG r (n + 1)) :
    programCount .divide (reciprocal d).program = programCount .divide d.program + 1 := by
  simpa [reciprocal] using build_count .divide d n (le_refl n)

/-- The new rational leaves are only zero and one; no arbitrary scalar leaf. -/
theorem reciprocal_otherRational_count {r n : ℕ} (d : DAG r (n + 1)) :
    programCount .otherRational (reciprocal d).program =
      programCount .otherRational d.program := by
  simpa only [reciprocal,
    ite_eq_right (by decide : CountKind.otherRational ≠ .divide), add_zero] using
    build_count .otherRational d n (le_refl n)

end
end ExactFourierCircuits.UniformReciprocalPreparation

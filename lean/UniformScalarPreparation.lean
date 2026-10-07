import UniformLocalShear

/-! Shared coefficient preparation.  Registers contain scalars only: the syntax
has neither array-input references nor conditional/complex-equality operations.
`Admissible` certifies partial divisions before `run` is used.  The same program
and output references prepare conjugates when supplied roots are conjugated. -/
namespace ExactFourierCircuits.UniformScalarPreparation
noncomputable section
open OAI.ExactFourier TypedKernelWords

/-- Every operand is a previously prepared register, not an expression tree. -/
inductive Instruction (roots prior : ℕ) where
  | rational (value : ℚ)
  | root (index : Fin roots)
  | add (left right : Fin prior)
  | sub (left right : Fin prior)
  | mul (left right : Fin prior)
  | divide (numerator denominator : Fin prior)

namespace Instruction

def eval {r k : ℕ} (i : Instruction r k)
    (roots : Fin r → ℂ) (values : Fin k → ℂ) : ℂ :=
  match i with
  | .rational q => q
  | .root j => roots j
  | .add j k => values j + values k
  | .sub j k => values j - values k
  | .mul j k => values j * values k
  | .divide j k => values j / values k

def Admissible {r k : ℕ} (i : Instruction r k) (values : Fin k → ℂ) : Prop :=
  match i with
  | .divide _ k => values k ≠ 0
  | _ => True

theorem eval_conjugate {r k : ℕ} (i : Instruction r k)
    (roots : Fin r → ℂ) (values : Fin k → ℂ) :
    i.eval (fun j => starRingEnd ℂ (roots j)) (fun j => starRingEnd ℂ (values j)) =
      starRingEnd ℂ (i.eval roots values) := by
  cases i <;> simp [eval, map_add, map_sub, map_mul, map_div₀]

theorem admissible_conjugate {r k : ℕ} (i : Instruction r k) (values : Fin k → ℂ) :
    i.Admissible (fun j => starRingEnd ℂ (values j)) ↔ i.Admissible values := by
  cases i <;> simp [Admissible]

end Instruction

/-- A finite DAG in topological register order.  Sharing uses repeated Fin refs. -/
inductive Program (roots : ℕ) : ℕ → Type where
  | nil : Program roots 0
  | step {prior : ℕ} (history : Program roots prior)
      (instruction : Instruction roots prior) : Program roots (prior + 1)

namespace Program

def eval {r : ℕ} : {k : ℕ} → Program r k → (Fin r → ℂ) → Fin k → ℂ
  | 0, .nil, _ => Fin.elim0
  | _ + 1, .step p i, roots =>
      let values := p.eval roots
      Fin.snoc values (i.eval roots values)

def Admissible {r : ℕ} : {k : ℕ} → Program r k → (Fin r → ℂ) → Prop
  | 0, .nil, _ => True
  | _ + 1, .step p i, roots => p.Admissible roots ∧ i.Admissible (p.eval roots)

/-- Certified evaluation; an unproved or zero denominator cannot be run. -/
def run {r k : ℕ} (p : Program r k) (roots : Fin r → ℂ)
    (_valid : p.Admissible roots) : Fin k → ℂ := p.eval roots

theorem eval_conjugate {r k : ℕ} (p : Program r k) (roots : Fin r → ℂ) :
    p.eval (fun j => starRingEnd ℂ (roots j)) =
      fun j => starRingEnd ℂ (p.eval roots j) := by
  induction p with
  | nil => funext j; exact Fin.elim0 j
  | step p i ih =>
      simp only [eval, ih, Instruction.eval_conjugate]
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

theorem admissible_conjugate {r k : ℕ} (p : Program r k) (roots : Fin r → ℂ) :
    p.Admissible (fun j => starRingEnd ℂ (roots j)) ↔ p.Admissible roots := by
  induction p with
  | nil => rfl
  | step p i ih =>
      simp only [Admissible, eval_conjugate, Instruction.admissible_conjugate, ih]

theorem run_conjugate {r k : ℕ} (p : Program r k) (roots : Fin r → ℂ)
    (valid : p.Admissible roots) :
    p.run (fun j => starRingEnd ℂ (roots j))
        ((p.admissible_conjugate roots).mpr valid) =
      fun j => starRingEnd ℂ (p.run roots valid j) := p.eval_conjugate roots

theorem eval_inverse_roots {r k : ℕ} (p : Program r k) (roots : Fin r → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) :
    p.eval (fun j => (roots j)⁻¹) = fun j => starRingEnd ℂ (p.eval roots j) := by
  have h : (fun j => (roots j)⁻¹) = fun j => starRingEnd ℂ (roots j) := by
    funext j
    exact Complex.inv_eq_conj (unit j)
  rw [h]
  exact p.eval_conjugate roots

theorem admissible_inverse_roots {r k : ℕ} (p : Program r k) (roots : Fin r → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) :
    p.Admissible (fun j => (roots j)⁻¹) ↔ p.Admissible roots := by
  have h : (fun j => (roots j)⁻¹) = fun j => starRingEnd ℂ (roots j) := by
    funext j
    exact Complex.inv_eq_conj (unit j)
  rw [h]
  exact p.admissible_conjugate roots

theorem eval_rootsOfUnity {r k : ℕ} (p : Program r k) (roots : Fin r → ℂ)
    (orders : Fin r → ℕ) (positive : ∀ j, orders j ≠ 0)
    (unity : ∀ j, (roots j) ^ orders j = 1) :
    p.eval (fun j => (roots j)⁻¹) = fun j => starRingEnd ℂ (p.eval roots j) :=
  p.eval_inverse_roots roots
    (fun j => Complex.norm_eq_one_of_pow_eq_one (unity j) (positive j))

theorem admissible_rootsOfUnity {r k : ℕ} (p : Program r k) (roots : Fin r → ℂ)
    (orders : Fin r → ℕ) (positive : ∀ j, orders j ≠ 0)
    (unity : ∀ j, (roots j) ^ orders j = 1) :
    p.Admissible (fun j => (roots j)⁻¹) ↔ p.Admissible roots :=
  p.admissible_inverse_roots roots
    (fun j => Complex.norm_eq_one_of_pow_eq_one (unity j) (positive j))

end Program

/-- Output registers may be reused arbitrarily without expanding the DAG. -/
structure DAG (roots outputs : ℕ) where
  length : ℕ
  program : Program roots length
  output : Fin outputs → Fin length

namespace DAG

def Admissible {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ) : Prop :=
  d.program.Admissible roots

def run {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (valid : d.Admissible roots) : Fin a → ℂ := fun j => d.program.run roots valid (d.output j)

theorem admissible_conjugate {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ) :
    d.Admissible (fun j => starRingEnd ℂ (roots j)) ↔ d.Admissible roots :=
  d.program.admissible_conjugate roots

theorem run_conjugate {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (valid : d.Admissible roots) :
    d.run (fun j => starRingEnd ℂ (roots j))
        ((d.admissible_conjugate roots).mpr valid) =
      fun j => starRingEnd ℂ (d.run roots valid j) := by
  funext j
  exact congrFun (d.program.run_conjugate roots valid) (d.output j)

theorem admissible_inverse_roots {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) :
    d.Admissible (fun j => (roots j)⁻¹) ↔ d.Admissible roots :=
  d.program.admissible_inverse_roots roots unit

theorem run_inverse_roots {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (valid : d.Admissible roots) :
    d.run (fun j => (roots j)⁻¹) ((d.admissible_inverse_roots roots unit).mpr valid) =
      fun j => starRingEnd ℂ (d.run roots valid j) := by
  funext j
  exact congrFun (d.program.eval_inverse_roots roots unit) (d.output j)

theorem admissible_rootsOfUnity {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (orders : Fin r → ℕ) (positive : ∀ j, orders j ≠ 0)
    (unity : ∀ j, (roots j) ^ orders j = 1) :
    d.Admissible (fun j => (roots j)⁻¹) ↔ d.Admissible roots :=
  d.program.admissible_rootsOfUnity roots orders positive unity

theorem run_rootsOfUnity {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (orders : Fin r → ℕ) (positive : ∀ j, orders j ≠ 0)
    (unity : ∀ j, (roots j) ^ orders j = 1) (valid : d.Admissible roots) :
    d.run (fun j => (roots j)⁻¹)
        ((d.admissible_rootsOfUnity roots orders positive unity).mpr valid) =
      fun j => starRingEnd ℂ (d.run roots valid j) := by
  funext j
  exact congrFun (d.program.eval_rootsOfUnity roots orders positive unity) (d.output j)

/-- Kappa uses the coefficient prepared by the second run of this exact DAG. -/
def preparedKappa {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (valid : d.Admissible roots) (j : Fin a) : ℂ :=
  1 + d.run roots valid j *
    d.run (fun j => starRingEnd ℂ (roots j))
      ((d.admissible_conjugate roots).mpr valid) j

theorem preparedKappa_eq {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (valid : d.Admissible roots) (j : Fin a) :
    d.preparedKappa roots valid j = UniformLocalShear.kappa (d.run roots valid j) := by
  exact congrArg (fun z : ℂ => 1 + d.run roots valid j * z)
    (congrFun (d.run_conjugate roots valid) j)

theorem preparedKappa_inverse_roots {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (valid : d.Admissible roots) (j : Fin a) :
    1 + d.run roots valid j *
        d.run (fun j => (roots j)⁻¹)
          ((d.admissible_inverse_roots roots unit).mpr valid) j =
      UniformLocalShear.kappa (d.run roots valid j) := by
  exact congrArg (fun z : ℂ => 1 + d.run roots valid j * z)
    (congrFun (d.run_inverse_roots roots unit valid) j)

theorem preparedKappa_ne_zero {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (valid : d.Admissible roots) (j : Fin a) : d.preparedKappa roots valid j ≠ 0 := by
  rw [preparedKappa_eq]
  exact UniformLocalShear.kappa_ne_zero _

theorem preparedSecond_ne_zero {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (valid : d.Admissible roots) (j : Fin a) :
    d.run roots valid j - d.preparedKappa roots valid j ≠ 0 := by
  rw [preparedKappa_eq]
  exact UniformLocalShear.second_ne_zero _

def shearWord {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (valid : d.Admissible roots) (j : Fin a) : List Step :=
  TypedKernelWords.shearWord (d.preparedKappa roots valid j)
      (d.preparedKappa_ne_zero roots valid j) ++
    TypedKernelWords.shearWord (d.run roots valid j - d.preparedKappa roots valid j)
      (d.preparedSecond_ne_zero roots valid j)

theorem shearWord_matrix {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (valid : d.Admissible roots) (j : Fin a) :
    wordMatrix (d.shearWord roots valid j) = upperShear (d.run roots valid j) := by
  rw [shearWord, wordMatrix_append, TypedKernelWords.shearWord_matrix,
    TypedKernelWords.shearWord_matrix, UniformLocalShear.upperShear_mul]
  congr 1
  ring

theorem shearWord_calls {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (valid : d.Admissible roots) (j : Fin a) :
    wordCalls (d.shearWord roots valid j) = 6 := by
  simp only [shearWord, wordCalls_append, TypedKernelWords.shearWord_calls]

end DAG
end
end ExactFourierCircuits.UniformScalarPreparation

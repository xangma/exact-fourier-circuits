import OAI.Computability.FourierCircuit.Core

set_option autoImplicit false

/- A finite RAM program for the stronger paper's operational claim.
   Syntax contains no arbitrary complex constants, functions or array primitives.
   Each instruction costs one unit. All heap entries must be written before use.
   Division is partial and confined to prepared, input-independent scalars;
   its nonzero guard is a semantic precondition, not a complex branch instruction. -/
namespace ExactFourierCircuits.UniformMachine
open OAI.ExactFourier
noncomputable section

inductive NatOp where
  | add | sub | mul | div | mod
  deriving DecidableEq, Repr

inductive FieldOp where
  | add | sub | mul | div
  deriving DecidableEq, Repr

/-- Input dependence is tracked conservatively, preventing data-data products. -/
structure Scalar where
  value : ℂ
  dependent : Bool

def Scalar.zero : Scalar := ⟨0, false⟩

inductive Instruction where
  | natLiteral (dst value : ℕ)
  | length (dst : ℕ)
  | natBinary (op : NatOp) (dst left right : ℕ)
  | scalarLiteral (dst : ℕ) (value : ℚ)
  | fieldBinary (op : FieldOp) (dst left right : ℕ)
  | input (dst index : ℕ)
  | root (dst order : ℕ)
  | loadNat (dst address : ℕ)
  | storeNat (address src : ℕ)
  | loadScalar (dst address : ℕ)
  | storeScalar (address src : ℕ)
  | output (index src : ℕ)
  | branchLT (left right yes no : ℕ)
  | jump (target : ℕ)
  | halt
  deriving DecidableEq

abbrev Program := List Instruction

structure State where
  pc : ℕ
  natReg : ℕ → ℕ
  scalarReg : ℕ → Scalar
  natHeap : ℕ → Option ℕ
  scalarHeap : ℕ → Option Scalar
  outputs : ℕ → Option ℂ
  rootOrders : List ℕ

def initial : State := ⟨0, fun _ => 0, fun _ => Scalar.zero,
  fun _ => none, fun _ => none, fun _ => none, []⟩

def next (s : State) : State := { s with pc := s.pc + 1 }

def writeNat (s : State) (r v : ℕ) : State :=
  { next s with natReg := Function.update s.natReg r v }

def writeScalar (s : State) (r : ℕ) (v : Scalar) : State :=
  { next s with scalarReg := Function.update s.scalarReg r v }

def evalNat : NatOp → ℕ → ℕ → Option ℕ
  | .add, a, b => some (a + b)
  | .sub, a, b => some (a - b)
  | .mul, a, b => some (a * b)
  | .div, a, b => if b = 0 then none else some (a / b)
  | .mod, a, b => if b = 0 then none else some (a % b)

def evalField : FieldOp → Scalar → Scalar → Option Scalar
  | .add, a, b => some ⟨a.value + b.value, a.dependent || b.dependent⟩
  | .sub, a, b => some ⟨a.value - b.value, a.dependent || b.dependent⟩
  | .mul, a, b => if a.dependent && b.dependent then none
      else some ⟨a.value * b.value, a.dependent || b.dependent⟩
  | .div, a, b => if a.dependent || b.dependent then none
      else if b.value = 0 then none else some ⟨a.value / b.value, false⟩

inductive StepResult where
  | running (state : State)
  | halted (state : State)
  | failed

/-- Explicit root provision is the only root primitive. Programs cannot branch on ℂ. -/
def step (p : Program) (n : ℕ) (x : Fin n → ℂ) (s : State) : StepResult :=
  match p[s.pc]? with
  | none => .failed
  | some .halt => .halted s
  | some (.natLiteral dst value) => .running (writeNat s dst value)
  | some (.length dst) => .running (writeNat s dst n)
  | some (.natBinary op dst left right) =>
      match evalNat op (s.natReg left) (s.natReg right) with
      | none => .failed
      | some value => .running (writeNat s dst value)
  | some (.scalarLiteral dst value) => .running (writeScalar s dst ⟨value, false⟩)
  | some (.fieldBinary op dst left right) =>
      match evalField op (s.scalarReg left) (s.scalarReg right) with
      | none => .failed
      | some value => .running (writeScalar s dst value)
  | some (.input dst index) =>
      if hi : s.natReg index < n then
        .running (writeScalar s dst ⟨x ⟨s.natReg index, hi⟩, true⟩)
      else .failed
  | some (.root dst order) =>
      if s.natReg order = 0 then .failed else
        .running { writeScalar s dst ⟨zeta (s.natReg order), false⟩ with
          rootOrders := s.rootOrders ++ [s.natReg order] }
  | some (.loadNat dst address) =>
      match s.natHeap (s.natReg address) with
      | none => .failed
      | some value => .running (writeNat s dst value)
  | some (.storeNat address src) => .running
      { next s with natHeap := Function.update s.natHeap (s.natReg address) (some (s.natReg src)) }
  | some (.loadScalar dst address) =>
      match s.scalarHeap (s.natReg address) with
      | none => .failed
      | some value => .running (writeScalar s dst value)
  | some (.storeScalar address src) => .running
      { next s with scalarHeap :=
          Function.update s.scalarHeap (s.natReg address) (some (s.scalarReg src)) }
  | some (.output index src) =>
      if s.natReg index < n then .running
        { next s with outputs :=
            Function.update s.outputs (s.natReg index) (some ((s.scalarReg src).value)) }
      else .failed
  | some (.branchLT left right yes no) => .running
      { s with pc := if s.natReg left < s.natReg right then yes else no }
  | some (.jump target) => .running { s with pc := target }

/-- A checked finite execution; its instruction count includes the halt. -/
inductive Executes (p : Program) (n : ℕ) (x : Fin n → ℂ) : State → ℕ → State → Prop where
  | halt {s : State} (h : step p n x s = .halted s) : Executes p n x s 1 s
  | next {s u v : State} {t : ℕ} (h : step p n x s = .running u)
      (tail : Executes p n x u t v) : Executes p n x s (t + 1) v

/-- This predicate bounds every integer and address touched by the execution. -/
def WordBound (B : ℕ) (s : State) : Prop :=
  s.pc ≤ B ∧ (∀ r, s.natReg r ≤ B) ∧
  (∀ a v, s.natHeap a = some v → a ≤ B ∧ v ≤ B) ∧
  (∀ a v, s.scalarHeap a = some v → a ≤ B) ∧
  (∀ a v, s.outputs a = some v → a ≤ B) ∧
  (∀ d ∈ s.rootOrders, d ≤ B)

/-- The bound covers intermediate states, including before each instruction. -/
inductive BoundedExecution (p : Program) (n : ℕ) (x : Fin n → ℂ) (B : ℕ) :
    State → ℕ → State → Prop where
  | halt {s : State} (bound : WordBound B s) (h : step p n x s = .halted s) :
      BoundedExecution p n x B s 1 s
  | next {s u v : State} {t : ℕ} (bound : WordBound B s)
      (h : step p n x s = .running u) (tail : BoundedExecution p n x B u t v) :
      BoundedExecution p n x B s (t + 1) v

theorem BoundedExecution.executes {p : Program} {n B t : ℕ} {x : Fin n → ℂ}
    {s v : State} (h : BoundedExecution p n x B s t v) : Executes p n x s t v := by
  induction h with
  | halt _ h => exact .halt h
  | next _ h _ ih => exact .next h ih

theorem BoundedExecution.final_bound {p : Program} {n B t : ℕ} {x : Fin n → ℂ}
    {s v : State} (h : BoundedExecution p n x B s t v) : WordBound B v := by
  induction h with
  | halt bound _ => exact bound
  | next _ _ _ ih => exact ih

theorem Executes.positive {p : Program} {n t : ℕ} {x : Fin n → ℂ}
    {s v : State} (h : Executes p n x s t v) : 0 < t := by
  cases h <;> omega

theorem Executes.deterministic {p : Program} {n t u : ℕ} {x : Fin n → ℂ}
    {s v w : State} (h : Executes p n x s t v) (h' : Executes p n x s u w) :
    t = u ∧ v = w := by
  induction h generalizing u w with
  | halt hh =>
      cases h' with
      | halt _ => exact ⟨rfl, rfl⟩
      | next hn _ => rw [hh] at hn; contradiction
  | next hn _ ih =>
      cases h' with
      | halt hh => rw [hn] at hh; contradiction
      | next hn' ht =>
          rw [hn] at hn'
          cases hn'
          obtain ⟨he, hs⟩ := ih ht
          exact ⟨congrArg (fun q : ℕ => q + 1) he, hs⟩

theorem initial_wordBound (B : ℕ) : WordBound B initial := by
  simp [WordBound, initial]

theorem evalField_mul_rejects_data (a b : ℂ) :
    evalField .mul ⟨a, true⟩ ⟨b, true⟩ = none := by
  simp [evalField]

theorem evalField_div_prepared (a b c : Scalar) (h : evalField .div a b = some c) :
    a.dependent = false ∧ b.dependent = false ∧ b.value ≠ 0 ∧ c.dependent = false := by
  simp only [evalField] at h
  split at h
  · contradiction
  · rename_i hab
    split at h
    · contradiction
    · rename_i hb
      simp only [Option.some.injEq] at h
      have hdeps : a.dependent = false ∧ b.dependent = false := by
        cases ha : a.dependent <;> cases hb' : b.dependent <;> simp_all
      subst c
      exact ⟨hdeps.1, hdeps.2, hb, rfl⟩

def ComputesDFT (n : ℕ) (x : Fin n → ℂ) (s : State) : Prop :=
  ∀ j : Fin n, s.outputs j.val = some ((fourierMatrix n).mulVec x j)

def asymptoticCost (theta : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * (Real.log (n : ℝ)) ^ theta *
    (Real.log (Real.log (n : ℝ))) ^ (4 - theta)

/-- One finite program, all input lengths, one specified root, and every charged
    preparation/field/address operation. This is a target, not a proved theorem. -/
def UniformDFTStatement (theta : ℝ) : Prop :=
  ∃ p : Program, ∃ K : ℝ, 0 < K ∧ ∃ N degree : ℕ, 3 ≤ N ∧ 0 < degree ∧
    ∀ n : ℕ, 0 < n → ∃ D : ℕ, 0 < D ∧ D < 1024 * n ^ 3 ∧
    ∀ x : Fin n → ℂ, ∃ t : ℕ, ∃ s : State,
      BoundedExecution p n x ((n + 2) ^ degree) initial t s ∧
      ComputesDFT n x s ∧ s.rootOrders = [D] ∧
      (N ≤ n → (t : ℝ) ≤ K * asymptoticCost theta n)

end
end ExactFourierCircuits.UniformMachine

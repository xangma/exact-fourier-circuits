import UniformMachineRuns

set_option autoImplicit false

/-! Instruction-level homogeneous-data admissibility. This refines successful
UniformMachine execution; it does not infer a certificate from final output
linearity. Prepared scalar arithmetic remains unrestricted. -/
namespace ExactFourierCircuits.DFTModelAdmissibility
open UniformMachine
noncomputable section

inductive Mode where
  | prepared
  | data
  deriving DecidableEq

/-- An untainted data slot must contain zero. A prepared slot can contain any
complex value, including nonzero coefficients. -/
def InMode : Mode → Scalar → Prop
  | .prepared, a => a.dependent = false
  | .data, a => a.dependent = false → a.value = 0

/-- The local obstruction to homogeneous addition/subtraction: if exactly one
operand is data, its prepared partner must be zero. -/
def MixedZero (a b : Scalar) : Prop :=
  (a.dependent = true → b.dependent = false → b.value = 0) ∧
  (b.dependent = true → a.dependent = false → a.value = 0)

/-- Tainted values vanish in an execution on zero input. -/
def ScalarZero (a : Scalar) : Prop := a.dependent = true → a.value = 0

structure StateZero (s : State) : Prop where
  registers : ∀ r, ScalarZero (s.scalarReg r)
  heap : ∀ a v, s.scalarHeap a = some v → ScalarZero v

/-- Only add/sub need the additional homogeneous mixing side condition;
successful multiplication/division already enforce their dependence guards. -/
def FieldGuard : FieldOp → Scalar → Scalar → Prop
  | .add, a, b => MixedZero a b
  | .sub, a, b => MixedZero a b
  | .mul, _, _ => True
  | .div, _, _ => True

def InstructionGuard (i : Instruction) (s : State) : Prop :=
  match i with
  | .fieldBinary op _ l r => FieldGuard op (s.scalarReg l) (s.scalarReg r)
  | _ => True

def Guard (p : Program) (s : State) : Prop :=
  ∀ i, p[s.pc]? = some i → InstructionGuard i s

theorem mixed_of_mode {m : Mode} {a b : Scalar}
    (ha : InMode m a) (hb : InMode m b) : MixedZero a b := by
  cases m with
  | prepared => simp_all [InMode,MixedZero]
  | data => exact ⟨fun _ h => hb h,fun _ h => ha h⟩

theorem zero_in_mode (m : Mode) : InMode m Scalar.zero := by
  cases m <;> simp [InMode,Scalar.zero]

theorem mode_add {m : Mode} {a b : Scalar} (ha : InMode m a) (hb : InMode m b) :
    InMode m ⟨a.value+b.value,a.dependent || b.dependent⟩ := by
  cases m with
  | prepared => simp_all [InMode]
  | data =>
      intro h
      have both : a.dependent = false ∧ b.dependent = false := by simpa using h
      simp [ha both.1,hb both.2]

theorem mode_sub {m : Mode} {a b : Scalar} (ha : InMode m a) (hb : InMode m b) :
    InMode m ⟨a.value-b.value,a.dependent || b.dependent⟩ := by
  cases m with
  | prepared => simp_all [InMode]
  | data =>
      intro h
      have both : a.dependent = false ∧ b.dependent = false := by simpa using h
      simp [ha both.1,hb both.2]

theorem mode_scale {m : Mode} {a b : Scalar} (_ha : a.dependent = false)
    (hb : InMode m b) :
    InMode m ⟨a.value*b.value,b.dependent⟩ := by
  cases m with
  | prepared => exact hb
  | data => intro h; simp [hb h]

theorem evalField_zero {op : FieldOp} {a b c : Scalar}
    (ha : ScalarZero a) (hb : ScalarZero b) (guard : FieldGuard op a b)
    (he : evalField op a b = some c) : ScalarZero c := by
  rcases a with ⟨av,ad⟩
  rcases b with ⟨bv,bd⟩
  rcases c with ⟨cv,cd⟩
  cases op <;> cases ad <;> cases bd <;>
    simp_all [ScalarZero,FieldGuard,MixedZero,evalField,Scalar.mk.injEq]

 theorem initial_zero : StateZero initial := by
  constructor
  · intro r; simp [ScalarZero,initial,Scalar.zero]
  · intro a v h; simp [initial] at h

 theorem StateZero.withPC {s : State} (h : StateZero s) (pc : ℕ) :
    StateZero {s with pc := pc} := ⟨h.registers,h.heap⟩

 theorem StateZero.writeNat {s : State} (h : StateZero s) (r v : ℕ) :
    StateZero (writeNat s r v) := ⟨h.registers,h.heap⟩

 theorem StateZero.writeScalar {s : State} (h : StateZero s) (r : ℕ) (v : Scalar)
    (hv : ScalarZero v) : StateZero (writeScalar s r v) := by
  constructor
  · intro j
    by_cases e : j = r
    · subst j; simpa [UniformMachine.writeScalar,UniformMachine.next] using hv
    · simpa [UniformMachine.writeScalar,UniformMachine.next,Function.update,e] using h.registers j
  · exact h.heap

 theorem StateZero.storeScalar {s : State} (h : StateZero s) (a : ℕ) (v : Scalar)
    (hv : ScalarZero v) :
    StateZero {next s with scalarHeap := Function.update s.scalarHeap a (some v)} := by
  constructor
  · exact h.registers
  · intro j w hw
    by_cases e : j = a
    · subst j
      simp only [Function.update_self,Option.some.injEq] at hw
      subst w
      exact hv
    · exact h.heap j w (by simpa [Function.update,e] using hw)

/-- Every successful actual instruction preserves the zero-data state when its
own add/sub operands satisfy the local guard. No output equation is assumed. -/
theorem step_zero {p : Program} {n : ℕ} {x : Fin n → ℂ} {s u : State}
    (inputZero : ∀ i, x i = 0) (hs : StateZero s) (guard : Guard p s)
    (run : step p n x s = .running u) : StateZero u := by
  cases code : p[s.pc]? with
  | none => simp [step,code] at run
  | some i =>
    have gi := guard i code
    cases i with
    | halt => simp [step,code] at run
    | natLiteral r v =>
        simp only [step,code,StepResult.running.injEq] at run
        subst u; exact hs.writeNat _ _
    | length r =>
        simp only [step,code,StepResult.running.injEq] at run
        subst u; exact hs.writeNat _ _
    | natBinary op r l b =>
        cases ev : evalNat op (s.natReg l) (s.natReg b) with
        | none => simp [step,code,ev] at run
        | some v =>
            simp only [step,code,ev,StepResult.running.injEq] at run
            subst u; exact hs.writeNat _ _
    | scalarLiteral r v =>
        simp only [step,code,StepResult.running.injEq] at run
        subst u; exact hs.writeScalar _ _ (by simp [ScalarZero])
    | fieldBinary op r l b =>
        cases ev : evalField op (s.scalarReg l) (s.scalarReg b) with
        | none => simp [step,code,ev] at run
        | some v =>
            simp only [step,code,ev,StepResult.running.injEq] at run
            subst u
            exact hs.writeScalar _ _ (evalField_zero (hs.registers l) (hs.registers b) gi ev)
    | input r j =>
        simp only [step,code] at run
        split at run
        · simp only [StepResult.running.injEq] at run
          subst u
          exact hs.writeScalar _ _ (by simp [ScalarZero,inputZero])
        · contradiction
    | root r j =>
        simp only [step,code] at run
        split at run
        · contradiction
        · simp only [StepResult.running.injEq] at run
          subst u
          have h := hs.writeScalar r ⟨OAI.ExactFourier.zeta (s.natReg j),false⟩ (by simp [ScalarZero])
          exact ⟨h.registers,h.heap⟩
    | loadNat r j =>
        cases ev : s.natHeap (s.natReg j) with
        | none => simp [step,code,ev] at run
        | some v =>
            simp only [step,code,ev,StepResult.running.injEq] at run
            subst u; exact hs.writeNat _ _
    | storeNat j r =>
        simp only [step,code,StepResult.running.injEq] at run
        subst u; exact ⟨hs.registers,hs.heap⟩
    | loadScalar r j =>
        cases ev : s.scalarHeap (s.natReg j) with
        | none => simp [step,code,ev] at run
        | some v =>
            simp only [step,code,ev,StepResult.running.injEq] at run
            subst u
            exact hs.writeScalar _ _ (hs.heap _ _ ev)
    | storeScalar j r =>
        simp only [step,code,StepResult.running.injEq] at run
        subst u
        exact hs.storeScalar _ _ (hs.registers r)
    | output j r =>
        simp only [step,code] at run
        split at run
        · simp only [StepResult.running.injEq] at run
          subst u; exact ⟨hs.registers,hs.heap⟩
        · contradiction
    | branchLT l r yes no =>
        simp only [step,code,StepResult.running.injEq] at run
        subst u; exact ⟨hs.registers,hs.heap⟩
    | jump pc =>
        simp only [step,code,StepResult.running.injEq] at run
        subst u; exact ⟨hs.registers,hs.heap⟩

/-- A certificate of every actual instruction in a finite segment. Guard is a
local arithmetic side condition; it is not a replacement for the real step. -/
inductive AdmissibleRuns (p : Program) (n : ℕ) (x : Fin n → ℂ) :
    State → ℕ → State → Prop where
  | refl (s : State) : AdmissibleRuns p n x s 0 s
  | next {s u v : State} {t : ℕ} (guard : Guard p s)
      (run : step p n x s = .running u)
      (tail : AdmissibleRuns p n x u t v) : AdmissibleRuns p n x s (t+1) v

 theorem AdmissibleRuns.runs {p : Program} {n t : ℕ} {x : Fin n → ℂ} {s u : State}
    (h : AdmissibleRuns p n x s t u) : Runs p n x s t u := by
  induction h with
  | refl s => exact .refl s
  | next _ run _ ih => exact .next run ih

 theorem AdmissibleRuns.trans {p : Program} {n t v : ℕ} {x : Fin n → ℂ}
    {s u w : State} (h : AdmissibleRuns p n x s t u)
    (g : AdmissibleRuns p n x u v w) : AdmissibleRuns p n x s (t+v) w := by
  induction h with
  | refl _ => simpa using g
  | next guard run _ ih =>
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using AdmissibleRuns.next guard run (ih g)

 theorem AdmissibleRuns.zero {p : Program} {n t : ℕ} {x : Fin n → ℂ} {s u : State}
    (h : AdmissibleRuns p n x s t u) (inputZero : ∀ i, x i = 0)
    (hs : StateZero s) : StateZero u := by
  induction h with
  | refl _ => exact hs
  | next guard run _ ih => exact ih (step_zero inputZero hs guard run)


theorem guard_of_code {p : Program} {s : State} {i : Instruction}
    (code : p[s.pc]? = some i) (h : InstructionGuard i s) : Guard p s := by
  intro j hj
  rw [code] at hj
  cases hj
  exact h

inductive AdmissibleExecution (p : Program) (n : ℕ) (x : Fin n → ℂ) :
    State → ℕ → State → Prop where
  | halt {s : State} (run : step p n x s = .halted s) : AdmissibleExecution p n x s 1 s
  | next {s u v : State} {t : ℕ} (guard : Guard p s)
      (run : step p n x s = .running u)
      (tail : AdmissibleExecution p n x u t v) : AdmissibleExecution p n x s (t+1) v

 theorem AdmissibleExecution.executes {p : Program} {n t : ℕ} {x : Fin n → ℂ} {s u : State}
    (h : AdmissibleExecution p n x s t u) : Executes p n x s t u := by
  induction h with
  | halt h => exact .halt h
  | next _ run _ ih => exact .next run ih

 theorem AdmissibleRuns.executes {p : Program} {n t v : ℕ} {x : Fin n → ℂ} {s u w : State}
    (h : AdmissibleRuns p n x s t u) (g : AdmissibleExecution p n x u v w) :
    AdmissibleExecution p n x s (t+v) w := by
  induction h with
  | refl _ => simpa using g
  | next guard run _ ih =>
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        AdmissibleExecution.next guard run (ih g)

 theorem AdmissibleExecution.zero {p : Program} {n t : ℕ} {x : Fin n → ℂ} {s u : State}
    (h : AdmissibleExecution p n x s t u) (inputZero : ∀ i, x i = 0)
    (hs : StateZero s) : StateZero u := by
  induction h with
  | halt _ => exact hs
  | next guard run _ ih => exact ih (step_zero inputZero hs guard run)

end
end ExactFourierCircuits.DFTModelAdmissibility

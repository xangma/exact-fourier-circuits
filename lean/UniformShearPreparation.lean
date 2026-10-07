import UniformScalarPreparation

/-! A shared scalar bank for the zero-free six-C compiler. Inverse roots are
computed from the supplied root bank. The conjugate replay overrides each root
leaf by a reference to that computed inverse, with no new supplied roots. -/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformShearPreparation
open UniformScalarPreparation
open scoped BigOperators
noncomputable section

structure Env (r a : ℕ) where
  length : ℕ
  program : Program r length
  mu : Fin a → Fin length
  zero : Fin length
  one : Fin length
  front : Fin length
  back : Fin length
  inverseRoots : Fin r → Fin length

namespace Env

def push {r a : ℕ} (e : Env r a) (i : Instruction r e.length) : Env r a where
  length := e.length + 1
  program := .step e.program i
  mu := fun j => (e.mu j).castSucc
  zero := e.zero.castSucc
  one := e.one.castSucc
  front := e.front.castSucc
  back := e.back.castSucc
  inverseRoots := fun j => (e.inverseRoots j).castSucc

@[simp] theorem push_old {r a : ℕ} (e : Env r a) (i : Instruction r e.length)
    (roots : Fin r → ℂ) (j : Fin e.length) :
    (e.push i).program.eval roots j.castSucc = e.program.eval roots j := by
  simp [push, Program.eval]

@[simp] theorem push_last {r a : ℕ} (e : Env r a) (i : Instruction r e.length)
    (roots : Fin r → ℂ) :
    (e.push i).program.eval roots (Fin.last e.length) = i.eval roots (e.program.eval roots) := by
  simp [push, Program.eval]

def Good {r a : ℕ} (e : Env r a) (roots : Fin r → ℂ) (mu : Fin a → ℂ) : Prop :=
  (∀ j, e.program.eval roots (e.mu j) = mu j) ∧
  e.program.eval roots e.zero = 0 ∧ e.program.eval roots e.one = 1 ∧
  e.program.eval roots e.front = 5 / 4 ∧ e.program.eval roots e.back = 4 / 5

def RootsGood {r a : ℕ} (e : Env r a) (roots : Fin r → ℂ) : Prop :=
  ∀ j, e.program.eval roots (e.inverseRoots j) = (roots j)⁻¹

theorem good_push {r a : ℕ} (e : Env r a) (i : Instruction r e.length)
    (roots : Fin r → ℂ) (mu : Fin a → ℂ) (he : e.Good roots mu) :
    (e.push i).Good roots mu := by
  rcases he with ⟨hm, hz, ho, hf, hb⟩
  exact ⟨fun j => by simpa [push, Program.eval] using hm j, by simpa [push, Program.eval] using hz,
    by simpa [push, Program.eval] using ho, by simpa [push, Program.eval] using hf, by simpa [push, Program.eval] using hb⟩

theorem rootsGood_push {r a : ℕ} (e : Env r a) (i : Instruction r e.length)
    (roots : Fin r → ℂ) (he : e.RootsGood roots) : (e.push i).RootsGood roots := by
  intro j; simpa [push, Program.eval] using he j

end Env

def initial {r a : ℕ} (d : DAG r a) : Env r a :=
  let p := Program.step d.program (.rational 0)
  let q := Program.step p (.rational 1)
  let s := Program.step q (.rational (5 / 4))
  let t := Program.step s (.rational (4 / 5))
  { length := d.length + 4, program := t,
    mu := fun j => (d.output j).castSucc.castSucc.castSucc.castSucc,
    zero := (Fin.last d.length).castSucc.castSucc.castSucc,
    one := (Fin.last (d.length + 1)).castSucc.castSucc,
    front := (Fin.last (d.length + 2)).castSucc,
    back := Fin.last (d.length + 3),
    inverseRoots := fun _ => (Fin.last d.length).castSucc.castSucc.castSucc }

theorem initial_good {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ) :
    (initial d).Good roots (fun j => d.program.eval roots (d.output j)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j; simp [initial, Program.eval]
  all_goals dsimp only [initial]
  all_goals norm_num [Program.eval, Instruction.eval]

theorem initial_admissible {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (hd : d.Admissible roots) : (initial d).program.Admissible roots := by
  simpa [initial, Program.Admissible, Instruction.Admissible, DAG.Admissible] using hd

def rootStep {r a : ℕ} (e : Env r a) (j : Fin r) : Env r a :=
  let p := e.push (.root j)
  let q := p.push (.divide p.one (Fin.last e.length))
  { q with inverseRoots := Function.update q.inverseRoots j (Fin.last p.length) }

theorem rootStep_length {r a : ℕ} (e : Env r a) (j : Fin r) :
    (rootStep e j).length = e.length + 2 := rfl

theorem rootStep_good {r a : ℕ} (e : Env r a) (j : Fin r)
    (roots : Fin r → ℂ) (mu : Fin a → ℂ) (he : e.Good roots mu) :
    (rootStep e j).Good roots mu := Env.good_push _ _ _ _ (Env.good_push _ _ _ _ he)

theorem rootStep_inverse {r a : ℕ} (e : Env r a) (j l : Fin r)
    (roots : Fin r → ℂ) (mu : Fin a → ℂ) (he : e.Good roots mu) :
    (rootStep e j).program.eval roots ((rootStep e j).inverseRoots l) =
      if l = j then (roots l)⁻¹ else e.program.eval roots (e.inverseRoots l) := by
  by_cases h : l = j
  · subst l
    simp [rootStep, Env.push, Program.eval, Instruction.eval, he.2.2.1]
  · simp [rootStep, h, Env.push, Program.eval]

theorem unit_ne_zero {r : ℕ} (roots : Fin r → ℂ) (unit : ∀ j, ‖roots j‖ = 1)
    (j : Fin r) : roots j ≠ 0 := by
  intro h
  have hu := unit j
  rw [h, norm_zero] at hu
  norm_num at hu

theorem rootStep_admissible {r a : ℕ} (e : Env r a) (j : Fin r)
    (roots : Fin r → ℂ) (unit : ∀ j, ‖roots j‖ = 1)
    (he : e.program.Admissible roots) : (rootStep e j).program.Admissible roots := by
  simpa [rootStep, Env.push, Program.Admissible, Instruction.Admissible, Program.eval,
    Instruction.eval] using And.intro he (unit_ne_zero roots unit j)

def rootSteps {r a : ℕ} (e : Env r a) : List (Fin r) → Env r a
  | [] => e
  | j :: js => rootSteps (rootStep e j) js

theorem rootSteps_length {r a : ℕ} (e : Env r a) (js : List (Fin r)) :
    (rootSteps e js).length = e.length + 2 * js.length := by
  induction js generalizing e with
  | nil => simp [rootSteps]
  | cons j js ih => rw [rootSteps, ih, rootStep_length]; simp; omega

theorem rootSteps_good {r a : ℕ} (e : Env r a) (js : List (Fin r))
    (roots : Fin r → ℂ) (mu : Fin a → ℂ) (he : e.Good roots mu) :
    (rootSteps e js).Good roots mu := by
  induction js generalizing e with
  | nil => exact he
  | cons j js ih => exact ih _ (rootStep_good _ _ _ _ he)

theorem rootSteps_inverse {r a : ℕ} (e : Env r a) (js : List (Fin r))
    (roots : Fin r → ℂ) (mu : Fin a → ℂ) (he : e.Good roots mu) (l : Fin r) :
    (rootSteps e js).program.eval roots ((rootSteps e js).inverseRoots l) =
      if l ∈ js then (roots l)⁻¹ else e.program.eval roots (e.inverseRoots l) := by
  induction js generalizing e with
  | nil => simp [rootSteps]
  | cons j js ih =>
    rw [rootSteps, ih _ (rootStep_good _ _ _ _ he), rootStep_inverse _ _ _ _ _ he]
    by_cases h : l = j <;> by_cases ht : l ∈ js <;> simp [List.mem_cons, h, ht]

theorem rootSteps_admissible {r a : ℕ} (e : Env r a) (js : List (Fin r))
    (roots : Fin r → ℂ) (unit : ∀ j, ‖roots j‖ = 1)
    (he : e.program.Admissible roots) : (rootSteps e js).program.Admissible roots := by
  induction js generalizing e with
  | nil => exact he
  | cons j js ih => exact ih _ (rootStep_admissible _ _ _ unit he)

def base {r a : ℕ} (d : DAG r a) : Env r a := rootSteps (initial d) (List.finRange r)

theorem base_length {r a : ℕ} (d : DAG r a) : (base d).length = d.length + 4 + 2 * r := by
  simp [base, rootSteps_length, initial]

theorem base_good {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ) :
    (base d).Good roots (fun j => d.program.eval roots (d.output j)) :=
  rootSteps_good _ _ _ _ (initial_good _ _)

theorem base_rootsGood {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ) :
    (base d).RootsGood roots := by
  intro j
  simpa [base] using rootSteps_inverse (initial d) (List.finRange r) roots _
    (initial_good d roots) j

theorem base_admissible {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) :
    (base d).program.Admissible roots := rootSteps_admissible _ _ _ unit (initial_admissible _ _ hd)

def overrideInstruction {r k l : ℕ} (i : Instruction r k)
    (refs : Fin k → Fin l) (inverseRoots : Fin r → Fin l) (zero : Fin l) : Instruction r l :=
  match i with
  | .rational q => .rational q
  | .root j => .add (inverseRoots j) zero
  | .add j k => .add (refs j) (refs k)
  | .sub j k => .sub (refs j) (refs k)
  | .mul j k => .mul (refs j) (refs k)
  | .divide j k => .divide (refs j) (refs k)

theorem override_eval {r k l : ℕ} (i : Instruction r k) (refs : Fin k → Fin l)
    (inverseRoots : Fin r → Fin l) (zero : Fin l) (roots : Fin r → ℂ)
    (values : Fin l → ℂ) (old : Fin k → ℂ) (hrefs : ∀ j, values (refs j) = old j)
    (hroots : ∀ j, values (inverseRoots j) = (roots j)⁻¹) (hz : values zero = 0) :
    (overrideInstruction i refs inverseRoots zero).eval roots values =
      i.eval (fun j => (roots j)⁻¹) old := by
  cases i <;> simp [overrideInstruction, Instruction.eval, hrefs, hroots, hz]

theorem override_admissible {r k l : ℕ} (i : Instruction r k) (refs : Fin k → Fin l)
    (inverseRoots : Fin r → Fin l) (zero : Fin l) (values : Fin l → ℂ)
    (old : Fin k → ℂ) (hrefs : ∀ j, values (refs j) = old j) :
    (overrideInstruction i refs inverseRoots zero).Admissible values ↔ i.Admissible old := by
  cases i <;> simp [overrideInstruction, Instruction.Admissible, hrefs]

structure Replay (r a k : ℕ) where
  env : Env r a
  refs : Fin k → Fin env.length

/-- Literal arithmetic replay; a root leaf becomes inverse-root-ref + zero. -/
def replay {r a : ℕ} : {k : ℕ} → Program r k → Env r a → Replay r a k
  | 0, .nil, e => ⟨e, Fin.elim0⟩
  | _ + 1, .step p i, e =>
    let q := replay p e
    let s := q.env.push (overrideInstruction i q.refs q.env.inverseRoots q.env.zero)
    ⟨s, Fin.snoc (fun j => (q.refs j).castSucc) (Fin.last q.env.length)⟩

theorem replay_length {r a k : ℕ} (p : Program r k) (e : Env r a) :
    (replay p e).env.length = e.length + k := by
  induction p with
  | nil => rfl
  | step p i ih => change (replay p e).env.length + 1 = _; rw [ih]; omega

theorem replay_good {r a k : ℕ} (p : Program r k) (e : Env r a)
    (roots : Fin r → ℂ) (mu : Fin a → ℂ) (he : e.Good roots mu) :
    (replay p e).env.Good roots mu := by
  induction p with
  | nil => exact he
  | step p i ih => exact Env.good_push _ _ _ _ ih

theorem replay_rootsGood {r a k : ℕ} (p : Program r k) (e : Env r a)
    (roots : Fin r → ℂ) (he : e.RootsGood roots) : (replay p e).env.RootsGood roots := by
  induction p with
  | nil => exact he
  | step p i ih => exact Env.rootsGood_push _ _ _ ih

theorem replay_eval {r a k : ℕ} (p : Program r k) (e : Env r a)
    (roots : Fin r → ℂ) (mu : Fin a → ℂ) (he : e.Good roots mu)
    (hr : e.RootsGood roots) (j : Fin k) :
    (replay p e).env.program.eval roots ((replay p e).refs j) =
      p.eval (fun j => (roots j)⁻¹) j := by
  induction p with
  | nil => exact Fin.elim0 j
  | step p i ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [replay.eq_2]
      dsimp only [Env.push]
      simp only [Program.eval, Fin.snoc_last]
      exact override_eval i _ _ _ _ _ _ ih
        (replay_rootsGood p e roots hr) (replay_good p e roots mu he).2.1
    · rw [replay.eq_2]
      dsimp only [Env.push]
      simpa only [Program.eval, Fin.snoc_castSucc] using ih j

theorem replay_admissible {r a k : ℕ} (p : Program r k) (e : Env r a)
    (roots : Fin r → ℂ) (mu : Fin a → ℂ) (he : e.Good roots mu)
    (hr : e.RootsGood roots) (ha : e.program.Admissible roots)
    (hp : p.Admissible (fun j => (roots j)⁻¹)) :
    (replay p e).env.program.Admissible roots := by
  induction p with
  | nil => exact ha
  | step p i ih =>
    change (replay p e).env.program.Admissible roots ∧ _
    refine ⟨ih hp.1, ?_⟩
    exact (override_admissible i _ _ _ _ _ (replay_eval p e roots mu he hr)).mpr hp.2

structure ScaleEnv (r a : ℕ) where
  env : Env r a
  conjugate : Fin a → Fin env.length
  rows : Fin a → Fin 6 → Fin env.length

namespace ScaleEnv

def push {r a : ℕ} (s : ScaleEnv r a) (i : Instruction r s.env.length) : ScaleEnv r a where
  env := s.env.push i
  conjugate := fun j => (s.conjugate j).castSucc
  rows := fun j q => (s.rows j q).castSucc

def Good {r a : ℕ} (s : ScaleEnv r a) (roots : Fin r → ℂ) (mu : Fin a → ℂ) : Prop :=
  s.env.Good roots mu ∧ ∀ j, s.env.program.eval roots (s.conjugate j) = starRingEnd ℂ (mu j)

theorem good_push {r a : ℕ} (s : ScaleEnv r a) (i : Instruction r s.env.length)
    (roots : Fin r → ℂ) (mu : Fin a → ℂ) (hs : s.Good roots mu) :
    (s.push i).Good roots mu := by
  refine ⟨Env.good_push _ _ _ _ hs.1, ?_⟩
  intro j
  simpa [push, Env.push, Program.eval] using hs.2 j

end ScaleEnv

def initialScale {r a : ℕ} (d : DAG r a) : ScaleEnv r a :=
  let q := replay d.program (base d)
  { env := q.env, conjugate := fun j => q.refs (d.output j), rows := fun _ _ => q.env.zero }

theorem initialScale_length {r a : ℕ} (d : DAG r a) :
    (initialScale d).env.length = 2 * d.length + 2 * r + 4 := by
  change (replay d.program (base d)).env.length = _
  rw [replay_length, base_length]
  omega

theorem initialScale_good {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) :
    (initialScale d).Good roots (fun j => d.program.eval roots (d.output j)) := by
  refine ⟨replay_good _ _ _ _ (base_good _ _), ?_⟩
  intro j
  change (replay d.program (base d)).env.program.eval roots
    ((replay d.program (base d)).refs (d.output j)) = _
  rw [replay_eval _ _ roots _ (base_good _ _) (base_rootsGood _ _),
    d.program.eval_inverse_roots roots unit]

theorem initialScale_admissible {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) :
    (initialScale d).env.program.Admissible roots :=
  replay_admissible _ _ roots _ (base_good _ _) (base_rootsGood _ _)
    (base_admissible _ _ unit hd) ((d.admissible_inverse_roots roots unit).mpr hd)

def rowExpected (mu : ℂ) : Fin 6 → ℂ :=
  ![UniformLocalShear.kappa mu, mu - UniformLocalShear.kappa mu,
    (5 / 4) / UniformLocalShear.kappa mu, (4 / 5) * UniformLocalShear.kappa mu,
    (5 / 4) / (mu - UniformLocalShear.kappa mu),
    (4 / 5) * (mu - UniformLocalShear.kappa mu)]

def scaleStep {r a : ℕ} (s : ScaleEnv r a) (j : Fin a) : ScaleEnv r a :=
  let p₁ := s.push (.mul (s.env.mu j) (s.conjugate j))
  let p₂ := p₁.push (.add p₁.env.one (Fin.last s.env.length))
  let k₂ := Fin.last p₁.env.length
  let p₃ := p₂.push (.sub (p₂.env.mu j) k₂)
  let rho₃ := Fin.last p₂.env.length
  let p₄ := p₃.push (.divide p₃.env.front k₂.castSucc)
  let p₅ := p₄.push (.mul p₄.env.back k₂.castSucc.castSucc)
  let p₆ := p₅.push (.divide p₅.env.front rho₃.castSucc.castSucc)
  let p₇ := p₆.push (.mul p₆.env.back rho₃.castSucc.castSucc.castSucc)
  let prepared : Fin 6 → Fin p₇.env.length :=
    ![k₂.castSucc.castSucc.castSucc.castSucc.castSucc,
      rho₃.castSucc.castSucc.castSucc.castSucc,
      (Fin.last p₃.env.length).castSucc.castSucc.castSucc,
      (Fin.last p₄.env.length).castSucc.castSucc,
      (Fin.last p₅.env.length).castSucc, Fin.last p₆.env.length]
  { p₇ with rows := Function.update p₇.rows j prepared }

theorem scaleStep_length {r a : ℕ} (s : ScaleEnv r a) (j : Fin a) :
    (scaleStep s j).env.length = s.env.length + 7 := rfl

theorem scaleStep_good {r a : ℕ} (s : ScaleEnv r a) (j : Fin a)
    (roots : Fin r → ℂ) (mu : Fin a → ℂ) (hs : s.Good roots mu) :
    (scaleStep s j).Good roots mu := by
  iterate 7 apply ScaleEnv.good_push
  exact hs

theorem scaleStep_rows {r a : ℕ} (s : ScaleEnv r a) (j l : Fin a) (q : Fin 6)
    (roots : Fin r → ℂ) (mu : Fin a → ℂ) (hs : s.Good roots mu) :
    (scaleStep s j).env.program.eval roots ((scaleStep s j).rows l q) =
      if l = j then rowExpected (mu l) q else s.env.program.eval roots (s.rows l q) := by
  by_cases h : l = j
  · subst l
    dsimp only [scaleStep, ScaleEnv.push, Env.push]
    simp only [Function.update_self]
    fin_cases q <;>
      norm_num [Program.eval, Instruction.eval, rowExpected, UniformLocalShear.kappa,
        hs.1.1, hs.1.2.1, hs.1.2.2.1, hs.1.2.2.2.1, hs.1.2.2.2.2, hs.2]
  · dsimp only [scaleStep, ScaleEnv.push, Env.push]
    simp [h, Program.eval]

theorem scaleStep_admissible {r a : ℕ} (s : ScaleEnv r a) (j : Fin a)
    (roots : Fin r → ℂ) (mu : Fin a → ℂ) (hs : s.Good roots mu)
    (ha : s.env.program.Admissible roots) : (scaleStep s j).env.program.Admissible roots := by
  dsimp only [scaleStep, ScaleEnv.push, Env.push]
  simpa [Program.Admissible, Instruction.Admissible, Program.eval, Instruction.eval,
    hs.1.1, hs.1.2.2.1, hs.2, and_assoc, UniformLocalShear.kappa] using
    (show s.env.program.Admissible roots ∧ UniformLocalShear.kappa (mu j) ≠ 0 ∧
      mu j - UniformLocalShear.kappa (mu j) ≠ 0 from
        ⟨ha, UniformLocalShear.kappa_ne_zero _, UniformLocalShear.second_ne_zero _⟩)

def scaleSteps {r a : ℕ} (s : ScaleEnv r a) : List (Fin a) → ScaleEnv r a
  | [] => s
  | j :: js => scaleSteps (scaleStep s j) js

theorem scaleSteps_length {r a : ℕ} (s : ScaleEnv r a) (js : List (Fin a)) :
    (scaleSteps s js).env.length = s.env.length + 7 * js.length := by
  induction js generalizing s with
  | nil => simp [scaleSteps]
  | cons j js ih => rw [scaleSteps, ih, scaleStep_length]; simp; omega

theorem scaleSteps_good {r a : ℕ} (s : ScaleEnv r a) (js : List (Fin a))
    (roots : Fin r → ℂ) (mu : Fin a → ℂ) (hs : s.Good roots mu) :
    (scaleSteps s js).Good roots mu := by
  induction js generalizing s with
  | nil => exact hs
  | cons j js ih => exact ih _ (scaleStep_good _ _ _ _ hs)

theorem scaleSteps_rows {r a : ℕ} (s : ScaleEnv r a) (js : List (Fin a))
    (roots : Fin r → ℂ) (mu : Fin a → ℂ) (hs : s.Good roots mu) (l : Fin a) (q : Fin 6) :
    (scaleSteps s js).env.program.eval roots ((scaleSteps s js).rows l q) =
      if l ∈ js then rowExpected (mu l) q else s.env.program.eval roots (s.rows l q) := by
  induction js generalizing s with
  | nil => simp [scaleSteps]
  | cons j js ih =>
    rw [scaleSteps, ih _ (scaleStep_good _ _ _ _ hs), scaleStep_rows _ _ _ _ _ _ hs]
    by_cases h : l = j <;> by_cases ht : l ∈ js <;> simp [List.mem_cons, h, ht]

theorem scaleSteps_admissible {r a : ℕ} (s : ScaleEnv r a) (js : List (Fin a))
    (roots : Fin r → ℂ) (mu : Fin a → ℂ) (hs : s.Good roots mu)
    (ha : s.env.program.Admissible roots) : (scaleSteps s js).env.program.Admissible roots := by
  induction js generalizing s with
  | nil => exact ha
  | cons j js ih =>
    exact ih _ (scaleStep_good _ _ _ _ hs) (scaleStep_admissible _ _ _ _ hs ha)

def complete {r a : ℕ} (d : DAG r a) : ScaleEnv r a :=
  scaleSteps (initialScale d) (List.finRange a)

theorem complete_length {r a : ℕ} (d : DAG r a) :
    (complete d).env.length = 2 * d.length + 2 * r + 7 * a + 4 := by
  rw [complete, scaleSteps_length, initialScale_length, List.length_finRange]
  omega

theorem complete_good {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) :
    (complete d).Good roots (fun j => d.program.eval roots (d.output j)) :=
  scaleSteps_good _ _ _ _ (initialScale_good _ _ unit)

theorem complete_rows {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (j : Fin a) (q : Fin 6) :
    (complete d).env.program.eval roots ((complete d).rows j q) =
      rowExpected (d.program.eval roots (d.output j)) q := by
  simpa [complete] using scaleSteps_rows (initialScale d) (List.finRange a) roots _
    (initialScale_good _ _ unit) j q

theorem complete_admissible {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) :
    (complete d).env.program.Admissible roots := scaleSteps_admissible _ _ _ _
      (initialScale_good _ _ unit) (initialScale_admissible _ _ unit hd)

def expected (mu : ℂ) : Fin 8 → ℂ :=
  ![mu, starRingEnd ℂ mu, UniformLocalShear.kappa mu, mu - UniformLocalShear.kappa mu,
    (5 / 4) / UniformLocalShear.kappa mu, (4 / 5) * UniformLocalShear.kappa mu,
    (5 / 4) / (mu - UniformLocalShear.kappa mu), (4 / 5) * (mu - UniformLocalShear.kappa mu)]

/-- Row order: mu, conjugate, kappa, rho, front/back kappa, front/back rho. -/
def table {r a : ℕ} (d : DAG r a) : DAG r (a * 8) where
  length := (complete d).env.length
  program := (complete d).env.program
  output i :=
    let jq := finProdFinEquiv.symm i
    if h₀ : jq.2.val = 0 then (complete d).env.mu jq.1
    else if h₁ : jq.2.val = 1 then (complete d).conjugate jq.1
    else (complete d).rows jq.1 ⟨jq.2.val - 2, by omega⟩

theorem table_length {r a : ℕ} (d : DAG r a) :
    (table d).length = 2 * d.length + 2 * r + 7 * a + 4 := complete_length d

theorem table_admissible {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) : (table d).Admissible roots :=
  complete_admissible d roots unit hd

theorem table_run {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) (j : Fin a) (q : Fin 8) :
    (table d).run roots (table_admissible d roots unit hd) (finProdFinEquiv (j, q)) =
      expected (d.run roots hd j) q := by
  have hm := (complete_good d roots unit).1.1 j
  have hc := (complete_good d roots unit).2 j
  have hs := complete_rows d roots unit j
  fin_cases q <;>
    simp [table, DAG.run, Program.run, expected, rowExpected, hm, hc, hs]

theorem table_length_bound {r a : ℕ} (d : DAG r a) :
    (table d).length ≤ 7 * (d.length + r + a + 1) := by
  rw [table_length]
  omega

theorem table_output_bound {r a : ℕ} (d : DAG r a) (j : Fin (a * 8)) :
    ((table d).output j).val < 7 * (d.length + r + a + 1) :=
  ((table d).output j).isLt.trans_le (table_length_bound d)

def operandsBound {r k : ℕ} (i : Instruction r k) (B : ℕ) : Prop :=
  match i with
  | .root j => j.val < B
  | .add j l | .sub j l | .mul j l | .divide j l => j.val < B ∧ l.val < B
  | .rational _ => True

theorem operandsBound_of_prior {r k : ℕ} (i : Instruction r k) {B : ℕ}
    (hr : r ≤ B) (hk : k ≤ B) : operandsBound i B := by
  cases i with
  | rational _ => trivial
  | root j => exact j.isLt.trans_le hr
  | add j l | sub j l | mul j l | divide j l =>
    exact ⟨j.isLt.trans_le hk, l.isLt.trans_le hk⟩

def referencesBound {r : ℕ} (B : ℕ) : {k : ℕ} → Program r k → Prop
  | 0, .nil => True
  | _ + 1, .step p i => referencesBound B p ∧ operandsBound i B

theorem referencesBound_of_length {r k B : ℕ} (p : Program r k)
    (hr : r ≤ B) (hk : k ≤ B) : referencesBound B p := by
  induction p with
  | nil => trivial
  | step p i ih => exact ⟨ih (by omega), operandsBound_of_prior i hr (by omega)⟩

theorem table_references_bound {r a : ℕ} (d : DAG r a) :
    referencesBound (7 * (d.length + r + a + 1)) (table d).program :=
  referencesBound_of_length _ (by omega) (table_length_bound d)

inductive CountKind where
  | rootRead
  | divide
  deriving DecidableEq

def instructionCount {r k : ℕ} (kind : CountKind) (i : Instruction r k) : ℕ :=
  match kind, i with
  | .rootRead, .root _ => 1
  | .divide, .divide _ _ => 1
  | _, _ => 0

def programCount {r : ℕ} (kind : CountKind) : {k : ℕ} → Program r k → ℕ
  | 0, .nil => 0
  | _ + 1, .step p i => programCount kind p + instructionCount kind i

theorem initial_count {r a : ℕ} (kind : CountKind) (d : DAG r a) :
    programCount kind (initial d).program = programCount kind d.program := by
  cases kind <;> simp [initial, programCount, instructionCount]

theorem rootStep_count {r a : ℕ} (kind : CountKind) (e : Env r a) (j : Fin r) :
    programCount kind (rootStep e j).program = programCount kind e.program + 1 := by
  cases kind <;> simp [rootStep, Env.push, programCount, instructionCount]

theorem rootSteps_count {r a : ℕ} (kind : CountKind) (e : Env r a) (js : List (Fin r)) :
    programCount kind (rootSteps e js).program = programCount kind e.program + js.length := by
  induction js generalizing e with
  | nil => simp [rootSteps]
  | cons j js ih => rw [rootSteps, ih, rootStep_count]; simp; omega

theorem base_count {r a : ℕ} (kind : CountKind) (d : DAG r a) :
    programCount kind (base d).program = programCount kind d.program + r := by
  rw [base, rootSteps_count, initial_count, List.length_finRange]

theorem override_count {r k l : ℕ} (kind : CountKind) (i : Instruction r k)
    (refs : Fin k → Fin l) (inverseRoots : Fin r → Fin l) (zero : Fin l) :
    instructionCount kind (overrideInstruction i refs inverseRoots zero) =
      if kind = .rootRead then 0 else instructionCount kind i := by
  cases kind <;> cases i <;> rfl

theorem replay_count {r a k : ℕ} (kind : CountKind) (p : Program r k) (e : Env r a) :
    programCount kind (replay p e).env.program = programCount kind e.program +
      if kind = .rootRead then 0 else programCount kind p := by
  induction p with
  | nil => cases kind <;> simp [replay, programCount]
  | step p i ih =>
    rw [replay.eq_2]
    change programCount kind (replay p e).env.program + instructionCount kind _ = _
    rw [ih, override_count]
    cases kind <;> simp [programCount]; omega

theorem scaleStep_count {r a : ℕ} (kind : CountKind) (s : ScaleEnv r a) (j : Fin a) :
    programCount kind (scaleStep s j).env.program = programCount kind s.env.program +
      if kind = .rootRead then 0 else 2 := by
  cases kind <;> simp [scaleStep, ScaleEnv.push, Env.push, programCount, instructionCount]

theorem scaleSteps_count {r a : ℕ} (kind : CountKind) (s : ScaleEnv r a) (js : List (Fin a)) :
    programCount kind (scaleSteps s js).env.program = programCount kind s.env.program +
      if kind = .rootRead then 0 else 2 * js.length := by
  induction js generalizing s with
  | nil => cases kind <;> simp [scaleSteps]
  | cons j js ih =>
    rw [scaleSteps, ih, scaleStep_count]
    cases kind <;> simp; omega

/-- Reads are of the same supplied Fin r bank; replay adds no root leaves. -/
theorem table_rootReads {r a : ℕ} (d : DAG r a) :
    programCount .rootRead (table d).program = programCount .rootRead d.program + r := by
  change programCount .rootRead (scaleSteps (initialScale d) (List.finRange a)).env.program = _
  rw [scaleSteps_count]
  change programCount .rootRead (replay d.program (base d)).env.program + _ = _
  rw [replay_count, base_count]
  simp

theorem table_divisions {r a : ℕ} (d : DAG r a) :
    programCount .divide (table d).program = 2 * programCount .divide d.program + r + 2 * a := by
  change programCount .divide (scaleSteps (initialScale d) (List.finRange a)).env.program = _
  rw [scaleSteps_count]
  change programCount .divide (replay d.program (base d)).env.program + _ = _
  rw [replay_count, base_count]
  simp
  omega

theorem rowExpected_ne_zero (mu : ℂ) (q : Fin 6) : rowExpected mu q ≠ 0 := by
  fin_cases q
  · exact UniformLocalShear.kappa_ne_zero mu
  · exact UniformLocalShear.second_ne_zero mu
  · exact div_ne_zero (by norm_num) (UniformLocalShear.kappa_ne_zero mu)
  · exact mul_ne_zero (by norm_num) (UniformLocalShear.kappa_ne_zero mu)
  · exact div_ne_zero (by norm_num) (UniformLocalShear.second_ne_zero mu)
  · exact mul_ne_zero (by norm_num) (UniformLocalShear.second_ne_zero mu)

def scaleValues {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) (j : Fin a) (q : Fin 6) : ℂ :=
  (complete d).env.program.run roots (complete_admissible d roots unit hd) ((complete d).rows j q)

theorem scaleValues_eq {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) (j : Fin a) (q : Fin 6) :
    scaleValues d roots unit hd j q = rowExpected (d.run roots hd j) q :=
  complete_rows d roots unit j q

theorem scaleValues_ne_zero {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) (j : Fin a) (q : Fin 6) :
    scaleValues d roots unit hd j q ≠ 0 := by
  rw [scaleValues_eq]
  exact rowExpected_ne_zero _ _

open OAI.ExactFourier TypedKernelWords

/-- The variable diagonals read the prepared front/back scalars. -/
def scaledWord (front back : ℂ) (hf : front ≠ 0) (hb : back ≠ 0) : List Step :=
  [diagonalStep front 1 hf one_ne_zero] ++
    hadamardWord ++ [diagonalStep (-3) 1 (by norm_num) one_ne_zero] ++
    hadamardWord ++ [diagonalStep 2 1 (by norm_num) one_ne_zero] ++ hadamardWord ++
    [diagonalStep (-1 / 8) (-1 / 6) (by norm_num) (by norm_num),
      diagonalStep back 1 hb one_ne_zero]

theorem scaledWord_eq (t : ℂ) (ht : t ≠ 0)
    (hf : (5 / 4) / t ≠ 0) (hb : (4 / 5) * t ≠ 0) :
    scaledWord ((5 / 4) / t) ((4 / 5) * t) hf hb = shearWord t ht := by
  have hfront : (5 / 4) / t = 5 / (4 * t) := div_div _ _ _
  have hback : (4 / 5) * t = 4 * t / 5 := by ring
  simp only [scaledWord, shearWord, hfront, hback]

theorem scaledWord_eq_of_values (t : ℂ) (ht : t ≠ 0) (front back : ℂ)
    (hf : front ≠ 0) (hb : back ≠ 0)
    (hfront : front = (5 / 4) / t) (hback : back = (4 / 5) * t) :
    scaledWord front back hf hb = shearWord t ht := by
  subst front
  subst back
  exact scaledWord_eq t ht _ _

def preparedWord {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) (j : Fin a) : List Step :=
  scaledWord (scaleValues d roots unit hd j 2) (scaleValues d roots unit hd j 3)
    (scaleValues_ne_zero _ _ _ _ _ _) (scaleValues_ne_zero _ _ _ _ _ _) ++
  scaledWord (scaleValues d roots unit hd j 4) (scaleValues d roots unit hd j 5)
    (scaleValues_ne_zero _ _ _ _ _ _) (scaleValues_ne_zero _ _ _ _ _ _)

theorem preparedWord_eq {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) (j : Fin a) :
    preparedWord d roots unit hd j = UniformLocalShear.word (d.run roots hd j) := by
  let mu := d.run roots hd j
  have hfrontK : scaleValues d roots unit hd j 2 = (5 / 4) / UniformLocalShear.kappa mu := by
    simpa [rowExpected, mu] using scaleValues_eq d roots unit hd j 2
  have hbackK : scaleValues d roots unit hd j 3 = (4 / 5) * UniformLocalShear.kappa mu := by
    simpa [rowExpected, mu] using scaleValues_eq d roots unit hd j 3
  have hfrontR : scaleValues d roots unit hd j 4 = (5 / 4) / (mu - UniformLocalShear.kappa mu) := by
    simpa [rowExpected, mu] using scaleValues_eq d roots unit hd j 4
  have hbackR : scaleValues d roots unit hd j 5 = (4 / 5) * (mu - UniformLocalShear.kappa mu) := by
    simpa [rowExpected, mu] using scaleValues_eq d roots unit hd j 5
  exact congrArg₂ List.append
    (scaledWord_eq_of_values _ (UniformLocalShear.kappa_ne_zero mu) _ _ _ _ hfrontK hbackK)
    (scaledWord_eq_of_values _ (UniformLocalShear.second_ne_zero mu) _ _ _ _ hfrontR hbackR)

theorem preparedWord_matrix {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) (j : Fin a) :
    wordMatrix (preparedWord d roots unit hd j) = upperShear (d.run roots hd j) := by
  rw [preparedWord_eq]
  exact UniformLocalShear.word_matrix _

theorem preparedWord_calls {r a : ℕ} (d : DAG r a) (roots : Fin r → ℂ)
    (unit : ∀ j, ‖roots j‖ = 1) (hd : d.Admissible roots) (j : Fin a) :
    wordCalls (preparedWord d roots unit hd j) = 6 := by
  rw [preparedWord_eq]
  exact UniformLocalShear.word_calls _


end
end ExactFourierCircuits.UniformShearPreparation

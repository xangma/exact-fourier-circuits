import UniformMachine

set_option autoImplicit false

namespace ExactFourierCircuits.UniformMachine

/-- Finite non-halting segments permit charged loop and subroutine composition. -/
inductive Runs (p : Program) (n : ℕ) (x : Fin n → ℂ) : State → ℕ → State → Prop where
  | refl (s : State) : Runs p n x s 0 s
  | next {s u v : State} {t : ℕ} (h : step p n x s = .running u)
      (tail : Runs p n x u t v) : Runs p n x s (t + 1) v

inductive BoundedRuns (p : Program) (n : ℕ) (x : Fin n → ℂ) (B : ℕ) :
    State → ℕ → State → Prop where
  | refl {s : State} (bound : WordBound B s) : BoundedRuns p n x B s 0 s
  | next {s u v : State} {t : ℕ} (bound : WordBound B s)
      (h : step p n x s = .running u) (tail : BoundedRuns p n x B u t v) :
      BoundedRuns p n x B s (t + 1) v

theorem Runs.trans {p : Program} {n t u : ℕ} {x : Fin n → ℂ} {s v w : State}
    (h : Runs p n x s t v) (h' : Runs p n x v u w) : Runs p n x s (t + u) w := by
  induction h with
  | refl _ => simpa using h'
  | next hs _ ih => simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Runs.next hs (ih h')

theorem Runs.executes {p : Program} {n t u : ℕ} {x : Fin n → ℂ} {s v w : State}
    (h : Runs p n x s t v) (h' : Executes p n x v u w) : Executes p n x s (t + u) w := by
  induction h with
  | refl _ => simpa using h'
  | next hs _ ih => simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Executes.next hs (ih h')

theorem BoundedRuns.runs {p : Program} {n B t : ℕ} {x : Fin n → ℂ} {s v : State}
    (h : BoundedRuns p n x B s t v) : Runs p n x s t v := by
  induction h with
  | refl _ => exact .refl _
  | next _ hs _ ih => exact .next hs ih

theorem BoundedRuns.initial_bound {p : Program} {n B t : ℕ} {x : Fin n → ℂ} {s v : State}
    (h : BoundedRuns p n x B s t v) : WordBound B s := by
  cases h with
  | refl h => exact h
  | next h _ _ => exact h

theorem BoundedRuns.final_bound {p : Program} {n B t : ℕ} {x : Fin n → ℂ} {s v : State}
    (h : BoundedRuns p n x B s t v) : WordBound B v := by
  induction h with
  | refl h => exact h
  | next _ _ _ ih => exact ih

theorem BoundedRuns.trans {p : Program} {n B t u : ℕ} {x : Fin n → ℂ} {s v w : State}
    (h : BoundedRuns p n x B s t v) (h' : BoundedRuns p n x B v u w) :
    BoundedRuns p n x B s (t + u) w := by
  induction h with
  | refl _ => simpa using h'
  | next hb hs _ ih =>
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using BoundedRuns.next hb hs (ih h')

theorem BoundedRuns.executes {p : Program} {n B t u : ℕ} {x : Fin n → ℂ} {s v w : State}
    (h : BoundedRuns p n x B s t v) (h' : BoundedExecution p n x B v u w) :
    BoundedExecution p n x B s (t + u) w := by
  induction h with
  | refl _ => simpa using h'
  | next hb hs _ ih =>
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using BoundedExecution.next hb hs (ih h')

theorem Runs.bounded_of_invariant {p : Program} {n B t : ℕ} {x : Fin n → ℂ} {s v : State}
    (I : State → Prop) (h : Runs p n x s t v) (hs : I s)
    (hb : ∀ s, I s → WordBound B s)
    (hp : ∀ s u, I s → step p n x s = .running u → I u) : BoundedRuns p n x B s t v := by
  induction h with
  | refl s => exact .refl (hb s hs)
  | next h _ ih => exact .next (hb _ hs) h (ih (hp _ _ hs h))

theorem Executes.bounded_of_invariant {p : Program} {n B t : ℕ} {x : Fin n → ℂ} {s v : State}
    (I : State → Prop) (h : Executes p n x s t v) (hs : I s)
    (hb : ∀ s, I s → WordBound B s)
    (hp : ∀ s u, I s → step p n x s = .running u → I u) : BoundedExecution p n x B s t v := by
  induction h with
  | halt h => exact .halt (hb _ hs) h
  | next h _ ih => exact .next (hb _ hs) h (ih (hp _ _ hs h))

theorem field_step_write {p : Program} {n dst left right : ℕ} {op : FieldOp}
    {x : Fin n → ℂ} {s u : State}
    (hpc : p[s.pc]? = some (.fieldBinary op dst left right))
    (h : step p n x s = .running u) : ∃ v, u = writeScalar s dst v := by
  simp only [step, hpc] at h
  cases hv : evalField op (s.scalarReg left) (s.scalarReg right) with
  | none => simp [hv] at h
  | some v =>
      simp only [hv, StepResult.running.injEq] at h
      exact ⟨v, h.symm⟩

theorem writeNat_bound (B : ℕ) (s : State) (r value : ℕ)
    (hs : WordBound B s) (hpc : s.pc + 1 ≤ B) (hv : value ≤ B) :
    WordBound B (writeNat s r value) := by
  obtain ⟨_, hreg, hnat, hscalar, hout, hroot⟩ := hs
  refine ⟨hpc, ?_, hnat, hscalar, hout, hroot⟩
  intro j
  by_cases hj : j = r
  · subst j; simpa [writeNat, next] using hv
  · simpa [writeNat, next, hj] using hreg j

theorem writeScalar_bound (B : ℕ) (s : State) (r : ℕ) (value : Scalar)
    (hs : WordBound B s) (hpc : s.pc + 1 ≤ B) :
    WordBound B (writeScalar s r value) := by
  obtain ⟨_, hreg, hnat, hscalar, hout, hroot⟩ := hs
  exact ⟨hpc, hreg, hnat, hscalar, hout, hroot⟩

theorem changePC_bound (B : ℕ) (s : State) (pc : ℕ)
    (hs : WordBound B s) (hpc : pc ≤ B) : WordBound B { s with pc := pc } := by
  obtain ⟨_, hreg, hnat, hscalar, hout, hroot⟩ := hs
  exact ⟨hpc, hreg, hnat, hscalar, hout, hroot⟩

theorem emit_bound (B : ℕ) (s : State) (index : ℕ) (value : ℂ) (pc : ℕ)
    (hs : WordBound B s) (hindex : index ≤ B) (hpc : pc ≤ B) :
    WordBound B { s with pc := pc, outputs := Function.update s.outputs index (some value) } := by
  obtain ⟨_, hreg, hnat, hscalar, hout, hroot⟩ := hs
  refine ⟨hpc, hreg, hnat, hscalar, ?_, hroot⟩
  intro a v ha
  by_cases h : a = index
  · simpa [h] using hindex
  · exact hout a v (by simpa [h] using ha)

end ExactFourierCircuits.UniformMachine

import DFTModelCacheNatProjectionCore

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheNatProjection
open UniformMachine
noncomputable section

/-- Only successful source steps are reflected. A scalar failure is not erased
into a theorem about a successful original execution. -/
theorem running_source {p : Program} {n : ℕ} {x : Fin n→ℂ} {s u : State}
    (noLength : NoLength p) (base : State)
    (actual : step p n x s=.running u) :
    step (project p) n x (state base s)=.running (state base u) := by
  cases selected:p[s.pc]? with
  | none=>simp only [step,selected] at actual;cases actual
  | some i=>
    have projected:=project_at p s.pc i selected
    cases i with
    | length dst=>exact False.elim (no_length_at noLength s.pc dst selected)
    | halt=>simp only [step,selected] at actual;cases actual
    | natLiteral d v=>
      simp only [step,selected,StepResult.running.injEq] at actual
      subst u
      simp only [step,projected,instruction,
        DFTModelCacheNatControl.Instruction.native,state,writeNat,next]
    | natBinary op d l r=>
      cases he:evalNat op (s.natReg l) (s.natReg r) with
      | none=>simp only [step,selected,he] at actual;cases actual
      | some v=>
        simp only [step,selected,he,StepResult.running.injEq] at actual
        subst u
        simp only [step,projected,instruction,
          DFTModelCacheNatControl.Instruction.native,state,writeNat,next,he]
    | loadNat d a=>
      cases he:s.natHeap (s.natReg a) with
      | none=>simp only [step,selected,he] at actual;cases actual
      | some v=>
        simp only [step,selected,he,StepResult.running.injEq] at actual
        subst u
        simp only [step,projected,instruction,
          DFTModelCacheNatControl.Instruction.native,state,writeNat,next,he]
    | storeNat a src=>
      simp only [step,selected,StepResult.running.injEq] at actual
      subst u
      simp only [step,projected,instruction,
        DFTModelCacheNatControl.Instruction.native,state,next]
    | branchLT l r yes no=>
      simp only [step,selected,StepResult.running.injEq] at actual
      subst u
      simp only [step,projected,instruction,
        DFTModelCacheNatControl.Instruction.native,state]
      rfl
    | jump target=>
      simp only [step,selected,StepResult.running.injEq] at actual
      subst u
      simp only [step,projected,instruction,
        DFTModelCacheNatControl.Instruction.native,state]
    | scalarLiteral d v=>
      simp only [step,selected,StepResult.running.injEq] at actual
      subst u
      simp only [step,projected,instruction,
        DFTModelCacheNatControl.Instruction.native,state,writeScalar,next]
    | fieldBinary op d l r=>
      cases he:evalField op (s.scalarReg l) (s.scalarReg r) with
      | none=>simp only [step,selected,he] at actual;cases actual
      | some v=>
        simp only [step,selected,he,StepResult.running.injEq] at actual
        subst u
        simp only [step,projected,instruction,
          DFTModelCacheNatControl.Instruction.native,state,writeScalar,next]
    | input d index=>
      simp only [step,selected] at actual
      split at actual
      · simp only [StepResult.running.injEq] at actual
        subst u
        simp only [step,projected,instruction,
          DFTModelCacheNatControl.Instruction.native,state,writeScalar,next]
      · cases actual
    | root d order=>
      simp only [step,selected] at actual
      split at actual
      · cases actual
      · simp only [StepResult.running.injEq] at actual
        subst u
        simp only [step,projected,instruction,
          DFTModelCacheNatControl.Instruction.native,state,writeScalar,next]
    | loadScalar d a=>
      cases he:s.scalarHeap (s.natReg a) with
      | none=>simp only [step,selected,he] at actual;cases actual
      | some v=>
        simp only [step,selected,he,StepResult.running.injEq] at actual
        subst u
        simp only [step,projected,instruction,
          DFTModelCacheNatControl.Instruction.native,state,writeScalar,next]
    | storeScalar a src=>
      simp only [step,selected,StepResult.running.injEq] at actual
      subst u
      simp only [step,projected,instruction,
        DFTModelCacheNatControl.Instruction.native,state,next]
    | output index src=>
      simp only [step,selected] at actual
      split at actual
      · simp only [StepResult.running.injEq] at actual
        subst u
        simp only [step,projected,instruction,
          DFTModelCacheNatControl.Instruction.native,state,next]
      · cases actual

theorem halt_selected {p : Program} {n : ℕ} {x : Fin n→ℂ} {s : State}
    (actual : step p n x s=.halted s) : p[s.pc]?=some .halt := by
  cases selected:p[s.pc]? with
  | none=>simp only [step,selected] at actual;cases actual
  | some i=>
    cases i <;> simp only [step,selected] at actual
    all_goals first | rfl | contradiction | (split at actual <;> contradiction)

theorem halted_source {p : Program} {n : ℕ} {x : Fin n→ℂ} {s : State}
    (base : State) (actual : step p n x s=.halted s) :
    step (project p) n x (state base s)=.halted (state base s) := by
  have selected:=project_at p s.pc .halt (halt_selected actual)
  simp only [step,show (state base s).pc=s.pc from rfl,selected,instruction,
    DFTModelCacheNatControl.Instruction.native]

theorem executes_source {p : Program} {n count : ℕ} {x : Fin n→ℂ} {s u : State}
    (noLength : NoLength p) (base : State) (actual : Executes p n x s count u) :
    Executes (project p) n x (state base s) count (state base u) := by
  induction actual with
  | halt h=>exact .halt (halted_source base h)
  | next h _ ih=>exact .next (running_source noLength base h) ih

theorem bounded_source_from {p : Program} {n B count : ℕ} {x : Fin n→ℂ} {s u : State}
    (noLength : NoLength p) (base : State) (initial : WordBound B base)
    (actual : BoundedExecution p n x B s count u) :
    BoundedExecution (project p) n x B (state base s) count (state base u) := by
  induction actual with
  | halt bound h=>exact .halt (state_wordBound initial bound) (halted_source base h)
  | next bound h _ ih=>exact .next (state_wordBound initial bound) (running_source noLength base h) ih

/-- Exact same charged count, final pc/Nat banks, original scalar/output/root
fields. The initial bound is derived from the genuine source execution. -/
theorem bounded_source {p : Program} {n B count : ℕ} {x : Fin n→ℂ} {s u : State}
    (noLength : NoLength p) (actual : BoundedExecution p n x B s count u) :
    BoundedExecution (project p) n x B s count (state s u) := by
  have initial : WordBound B s := by cases actual <;> assumption
  simpa only [state_self] using bounded_source_from noLength s initial actual

theorem runs_source {p : Program} {n count : ℕ} {x : Fin n→ℂ} {s u : State}
    (noLength : NoLength p) (base : State) (actual : Runs p n x s count u) :
    Runs (project p) n x (state base s) count (state base u) := by
  induction actual with
  | refl s=>exact .refl _
  | next h _ ih=>exact .next (running_source noLength base h) ih

theorem bounded_runs_source_from {p : Program} {n B count : ℕ} {x : Fin n→ℂ} {s u : State}
    (noLength : NoLength p) (base : State) (initial : WordBound B base)
    (actual : BoundedRuns p n x B s count u) :
    BoundedRuns (project p) n x B (state base s) count (state base u) := by
  induction actual with
  | refl bound=>exact .refl (state_wordBound initial bound)
  | next bound h _ ih=>exact .next (state_wordBound initial bound) (running_source noLength base h) ih

theorem bounded_runs_source {p : Program} {n B count : ℕ} {x : Fin n→ℂ} {s u : State}
    (noLength : NoLength p) (actual : BoundedRuns p n x B s count u) :
    BoundedRuns (project p) n x B s count (state s u) := by
  simpa only [state_self] using bounded_runs_source_from noLength s actual.initial_bound actual

end
end ExactFourierCircuits.DFTModelCacheNatProjection

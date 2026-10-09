import UniformMachineRuns

set_option autoImplicit false

/-! Input-independent control and prepared values for actual successful machine
executions. Unlike the homogeneous guard refinement, this permits affine
intermediates and applies to every UniformMachine program. -/
namespace ExactFourierCircuits.DFTModelAdmissibilityControl
open UniformMachine
noncomputable section

structure ScalarMatch (a z : Scalar) : Prop where
  flags : a.dependent = z.dependent
  prepared : a.dependent = false → a.value = z.value

 theorem ScalarMatch.refl (a : Scalar) : ScalarMatch a a := ⟨rfl,fun _ => rfl⟩
 theorem ScalarMatch.data (a z : ℂ) : ScalarMatch ⟨a,true⟩ ⟨z,true⟩ :=
  ⟨rfl,by simp⟩
 theorem ScalarMatch.eq_of_prepared {a z : Scalar} (h : ScalarMatch a z)
    (ha : a.dependent = false) : a = z := by
  rcases a with ⟨av,ad⟩
  rcases z with ⟨zv,zd⟩
  obtain ⟨flags,values⟩ := h
  simp only at flags values ha
  cases flags
  rw [values ha]

 theorem evalField_match {op : FieldOp} {a b az bz c : Scalar}
    (ha : ScalarMatch a az) (hb : ScalarMatch b bz)
    (run : evalField op a b = some c) :
    ∃ cz, evalField op az bz = some cz ∧ ScalarMatch c cz := by
  cases op with
  | add =>
      simp only [evalField,Option.some.injEq] at run
      subst c
      refine ⟨_,rfl,⟨by simp [ha.flags,hb.flags],?_⟩⟩
      intro h
      have hh : a.dependent = false ∧ b.dependent = false := by simpa using h
      simp [ha.prepared hh.1,hb.prepared hh.2]
  | sub =>
      simp only [evalField,Option.some.injEq] at run
      subst c
      refine ⟨_,rfl,⟨by simp [ha.flags,hb.flags],?_⟩⟩
      intro h
      have hh : a.dependent = false ∧ b.dependent = false := by simpa using h
      simp [ha.prepared hh.1,hb.prepared hh.2]
  | mul =>
      simp only [evalField] at run
      split at run
      · contradiction
      · rename_i allowed
        simp only [Option.some.injEq] at run
        subst c
        refine ⟨⟨az.value*bz.value,az.dependent || bz.dependent⟩,?_,
          ⟨by simp [ha.flags,hb.flags],?_⟩⟩
        · simp [evalField,←ha.flags,←hb.flags,allowed]
        · intro h
          have hh : a.dependent = false ∧ b.dependent = false := by simpa using h
          simp [ha.prepared hh.1,hb.prepared hh.2]
  | div =>
      obtain ⟨a0,b0,_,_⟩ := evalField_div_prepared a b c run
      have ae := ha.eq_of_prepared a0
      have be := hb.eq_of_prepared b0
      subst az
      subst bz
      exact ⟨c,run,ScalarMatch.refl c⟩

inductive CellMatch : Option Scalar → Option Scalar → Prop where
  | none : CellMatch none none
  | some {a z : Scalar} (values : ScalarMatch a z) : CellMatch (some a) (some z)

 theorem CellMatch.refl (a : Option Scalar) : CellMatch a a := by
  cases a with
  | none => exact .none
  | some a => exact .some (ScalarMatch.refl a)

 theorem CellMatch.left {a z : Option Scalar} (h : CellMatch a z) {v : Scalar}
    (present : a = Option.some v) : ∃ w, z = Option.some w ∧ ScalarMatch v w := by
  cases h with
  | none => contradiction
  | some values => cases present; exact ⟨_,rfl,values⟩

 theorem CellMatch.right {a z : Option Scalar} (h : CellMatch a z) {v : Scalar}
    (present : z = Option.some v) : ∃ w, a = Option.some w ∧ ScalarMatch w v := by
  cases h with
  | none => contradiction
  | some values => cases present; exact ⟨_,rfl,values⟩

structure StateMatch (s z : State) : Prop where
  pc : z.pc = s.pc
  natReg : z.natReg = s.natReg
  natHeap : z.natHeap = s.natHeap
  scalarReg : ∀ r, ScalarMatch (s.scalarReg r) (z.scalarReg r)
  scalarHeap : ∀ a, CellMatch (s.scalarHeap a) (z.scalarHeap a)
  outputs : ∀ a, (s.outputs a).isSome = (z.outputs a).isSome
  roots : z.rootOrders = s.rootOrders

 theorem StateMatch.refl (s : State) : StateMatch s s :=
  ⟨rfl,rfl,rfl,fun _ => ScalarMatch.refl _,fun _ => CellMatch.refl _,fun _ => rfl,rfl⟩

 theorem StateMatch.withPC {s z : State} (h : StateMatch s z) (pc : ℕ) :
    StateMatch {s with pc := pc} {z with pc := pc} :=
  ⟨rfl,h.natReg,h.natHeap,h.scalarReg,h.scalarHeap,h.outputs,h.roots⟩

 theorem StateMatch.writeNat {s z : State} (h : StateMatch s z) (r v : ℕ) :
    StateMatch (UniformMachine.writeNat s r v) (UniformMachine.writeNat z r v) := by
  exact ⟨congrArg (fun k => k+1) h.pc,(by simpa only [UniformMachine.writeNat,UniformMachine.next] using congrArg (fun f : ℕ → ℕ => Function.update f r v) h.natReg),
    h.natHeap,h.scalarReg,h.scalarHeap,h.outputs,h.roots⟩

 theorem StateMatch.writeScalar {s z : State} (h : StateMatch s z) (r : ℕ)
    {v vz : Scalar} (values : ScalarMatch v vz) :
    StateMatch (UniformMachine.writeScalar s r v) (UniformMachine.writeScalar z r vz) := by
  refine ⟨congrArg (fun k => k+1) h.pc,h.natReg,h.natHeap,?_,h.scalarHeap,h.outputs,h.roots⟩
  intro j
  by_cases e : j = r
  · subst j; simpa only [UniformMachine.writeScalar,UniformMachine.next,
      Function.update_self] using values
  · simpa only [UniformMachine.writeScalar,UniformMachine.next,
      Function.update_of_ne e] using h.scalarReg j

 theorem StateMatch.storeNat {s z : State} (h : StateMatch s z) (a v : ℕ) :
    StateMatch {next s with natHeap := Function.update s.natHeap a (some v)}
      {next z with natHeap := Function.update z.natHeap a (some v)} :=
  ⟨congrArg (fun k => k+1) h.pc,h.natReg,
    congrArg (fun f => Function.update f a (some v)) h.natHeap,
    h.scalarReg,h.scalarHeap,h.outputs,h.roots⟩

 theorem StateMatch.storeScalar {s z : State} (h : StateMatch s z) (a : ℕ)
    {v vz : Scalar} (values : ScalarMatch v vz) :
    StateMatch {next s with scalarHeap := Function.update s.scalarHeap a (some v)}
      {next z with scalarHeap := Function.update z.scalarHeap a (some vz)} := by
  refine ⟨congrArg (fun k => k+1) h.pc,h.natReg,h.natHeap,h.scalarReg,?_,h.outputs,h.roots⟩
  intro j
  by_cases e : j = a
  · subst j; simpa only [UniformMachine.next,Function.update_self] using CellMatch.some values
  · simpa only [UniformMachine.next,Function.update_of_ne e] using h.scalarHeap j

 theorem StateMatch.output {s z : State} (h : StateMatch s z) (a : ℕ) (v vz : ℂ) :
    StateMatch {next s with outputs := Function.update s.outputs a (some v)}
      {next z with outputs := Function.update z.outputs a (some vz)} := by
  refine ⟨congrArg (fun k => k+1) h.pc,h.natReg,h.natHeap,h.scalarReg,h.scalarHeap,?_,h.roots⟩
  intro j
  by_cases e : j = a
  · subst j; simp only [Function.update_self,Option.isSome_some]
  · simpa only [UniformMachine.next,Function.update_of_ne e] using h.outputs j

 theorem StateMatch.root {s z : State} (h : StateMatch s z) (r d : ℕ) :
    StateMatch {UniformMachine.writeScalar s r ⟨OAI.ExactFourier.zeta d,false⟩ with rootOrders := s.rootOrders++[d]}
      {UniformMachine.writeScalar z r ⟨OAI.ExactFourier.zeta d,false⟩ with rootOrders := z.rootOrders++[d]} := by
  have w := h.writeScalar r (ScalarMatch.refl ⟨OAI.ExactFourier.zeta d,false⟩)
  exact ⟨w.pc,w.natReg,w.natHeap,w.scalarReg,w.scalarHeap,w.outputs,
    congrArg (fun ds => ds++[d]) h.roots⟩

/-- Every successful instruction has a counterpart on arbitrary other input.
The branch, address and dependence guards cannot inspect the data values. -/
theorem step_match {p : Program} {n : ℕ} {x y : Fin n → ℂ} {s z u : State}
    (same : StateMatch s z) (run : step p n x s = .running u) :
    ∃ uz, step p n y z = .running uz ∧ StateMatch u uz := by
  cases code : p[s.pc]? with
  | none => simp [step,code] at run
  | some i =>
    have zcode : p[z.pc]? = some i := by rw [same.pc]; exact code
    cases i with
    | halt => simp [step,code] at run
    | natLiteral r v =>
        simp only [step,code,StepResult.running.injEq] at run
        subst u
        exact ⟨_,by simp [step,zcode],same.writeNat _ _⟩
    | length r =>
        simp only [step,code,StepResult.running.injEq] at run
        subst u
        exact ⟨_,by simp [step,zcode],same.writeNat _ _⟩
    | natBinary op r l b =>
        cases ev : evalNat op (s.natReg l) (s.natReg b) with
        | none => simp [step,code,ev] at run
        | some v =>
            simp only [step,code,ev,StepResult.running.injEq] at run
            subst u
            exact ⟨_,by simp [step,zcode,same.natReg,ev],same.writeNat _ _⟩
    | scalarLiteral r v =>
        simp only [step,code,StepResult.running.injEq] at run
        subst u
        exact ⟨_,by simp [step,zcode],same.writeScalar _ (ScalarMatch.refl _)⟩
    | fieldBinary op r l b =>
        cases ev : evalField op (s.scalarReg l) (s.scalarReg b) with
        | none => simp [step,code,ev] at run
        | some v =>
            simp only [step,code,ev,StepResult.running.injEq] at run
            subst u
            obtain ⟨vz,e,matchv⟩ := evalField_match (same.scalarReg l) (same.scalarReg b) ev
            exact ⟨_,by simp [step,zcode,e],same.writeScalar _ matchv⟩
    | input r j =>
        simp only [step,code] at run
        split at run
        · rename_i bound
          simp only [StepResult.running.injEq] at run
          subst u
          refine ⟨UniformMachine.writeScalar z r ⟨y ⟨s.natReg j,bound⟩,true⟩,?_,
            same.writeScalar _ (ScalarMatch.data _ _)⟩
          simp [step,zcode,same.natReg,bound]
        · contradiction
    | root r j =>
        simp only [step,code] at run
        split at run
        · contradiction
        · rename_i positive
          simp only [StepResult.running.injEq] at run
          subst u
          exact ⟨_,by simp [step,zcode,same.natReg,positive],same.root _ _⟩
    | loadNat r j =>
        cases ev : s.natHeap (s.natReg j) with
        | none => simp [step,code,ev] at run
        | some v =>
            simp only [step,code,ev,StepResult.running.injEq] at run
            subst u
            exact ⟨_,by simp [step,zcode,same.natReg,same.natHeap,ev],same.writeNat _ _⟩
    | storeNat j r =>
        simp only [step,code,StepResult.running.injEq] at run
        subst u
        exact ⟨_,by simp [step,zcode,same.natReg],same.storeNat _ _⟩
    | loadScalar r j =>
        cases ev : s.scalarHeap (s.natReg j) with
        | none => simp [step,code,ev] at run
        | some v =>
            simp only [step,code,ev,StepResult.running.injEq] at run
            subst u
            obtain ⟨vz,ze,matchv⟩ := (same.scalarHeap _).left ev
            exact ⟨_,by simp [step,zcode,same.natReg,ze],same.writeScalar _ matchv⟩
    | storeScalar j r =>
        simp only [step,code,StepResult.running.injEq] at run
        subst u
        refine ⟨_,?_,same.storeScalar (s.natReg j) (same.scalarReg r)⟩
        simp [step,zcode,same.natReg]
    | output j r =>
        simp only [step,code] at run
        split at run
        · rename_i bound
          simp only [StepResult.running.injEq] at run
          subst u
          exact ⟨_,by simp [step,zcode,same.natReg,bound],same.output (s.natReg j) (s.scalarReg r).value (z.scalarReg r).value⟩
        · contradiction
    | branchLT l r yes no =>
        simp only [step,code,StepResult.running.injEq] at run
        subst u
        exact ⟨_,by simp [step,zcode,same.natReg],same.withPC _⟩
    | jump pc =>
        simp only [step,code,StepResult.running.injEq] at run
        subst u
        exact ⟨_,by simp [step,zcode],same.withPC _⟩

 theorem halt_code {p : Program} {n : ℕ} {x : Fin n → ℂ} {s : State}
    (run : step p n x s = .halted s) : p[s.pc]? = some .halt := by
  cases code : p[s.pc]? with
  | none => simp [step,code] at run
  | some i =>
      cases i <;> simp only [step,code] at run
      all_goals first | rfl | contradiction | (split at run <;> contradiction)

 theorem StateMatch.wordBound {s z : State} {B : ℕ} (same : StateMatch s z)
    (bound : WordBound B s) : WordBound B z := by
  refine ⟨by simpa [same.pc] using bound.1,?_,?_,?_,?_,?_⟩
  · intro r; simpa [same.natReg] using bound.2.1 r
  · intro a v present
    exact bound.2.2.1 a v (by simpa [same.natHeap] using present)
  · intro a v present
    obtain ⟨w,sw,_⟩ := (same.scalarHeap a).right present
    exact bound.2.2.2.1 a w sw
  · intro a v present
    cases sv : s.outputs a with
    | none => have h := same.outputs a; simp [sv,present] at h
    | some w => exact bound.2.2.2.2.1 a w sv
  · intro d hd
    exact bound.2.2.2.2.2 d (by simpa [same.roots] using hd)

/-- Same real instruction count and every intermediate word bound, for any
other data input. This is an operational theorem, not a DFT output argument. -/
theorem boundedExecution_match {p : Program} {n B ticks : ℕ} {x y : Fin n → ℂ}
    {s z u : State} (run : BoundedExecution p n x B s ticks u) (same : StateMatch s z) :
    ∃ uz, BoundedExecution p n y B z ticks uz ∧ StateMatch u uz := by
  induction run generalizing z with
  | halt bound halted =>
      exact ⟨z,.halt (same.wordBound bound) (by simp [step,same.pc,halt_code halted]),same⟩
  | next bound step tail ih =>
      obtain ⟨mid,midRun,midSame⟩ := step_match same step
      obtain ⟨uz,rest,last⟩ := ih midSame
      exact ⟨uz,.next (same.wordBound bound) midRun rest,last⟩

 theorem initial_execution_match {p : Program} {n B ticks : ℕ} {x y : Fin n → ℂ} {u : State}
    (run : BoundedExecution p n x B initial ticks u) :
    ∃ uz, BoundedExecution p n y B initial ticks uz ∧ StateMatch u uz :=
  boundedExecution_match run (StateMatch.refl initial)

end
end ExactFourierCircuits.DFTModelAdmissibilityControl

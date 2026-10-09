import UniformAssembly
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveRegisterFrames
open UniformMachine
/-- The literal instruction does not write this Nat register. -/
def Avoids (r:ℕ) : Instruction→Prop
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _ =>d≠r
 | _=>True
instance (r : ℕ) (i : Instruction) : Decidable (Avoids r i) := by
 cases i <;> unfold Avoids <;> infer_instance
lemma append_iff (r : ℕ) (p q : Program) :
 (∀i∈p++q,Avoids r i) ↔ (∀i∈p,Avoids r i) ∧ (∀i∈q,Avoids r i):=by
 simp only [List.mem_append,or_imp,forall_and]
lemma relocated_iff (r base ret : ℕ) (p : Program) :
 (∀i∈p.map (UniformAssembly.relocate base ret),Avoids r i) ↔ (∀i∈p,Avoids r i):=by
 simp only [List.forall_mem_map]
 have eq : ∀i,Avoids r (UniformAssembly.relocate base ret i)=Avoids r i:=by
  intro i;cases i <;> rfl
 simp only [eq]
lemma step_keep (p:Program) (n r:ℕ) (x:Fin n→ℂ) (s u:State)
 (code:∀i∈p,Avoids r i) (run:step p n x s=.running u) : u.natReg r=s.natReg r:=by
 cases hp:p[s.pc]? with
 | none=>simp [step,hp] at run
 | some ins=>
  have safe:=code ins (List.mem_of_getElem? hp)
  cases ins <;> simp only [Avoids] at safe
  all_goals simp only [step,hp] at run
  all_goals first
   | (cases run; rfl)
   | (cases run; simp [writeNat, next, Ne.symm safe])
   | (split at run <;> simp_all [writeScalar,next])
   | (split at run <;> simp_all [writeNat,next,Ne.symm safe])
   | (cases run)
  all_goals cases run
  all_goals first | simp [writeNat,next,Ne.symm safe] | rfl
lemma code_of_all (r : ℕ) (p : Program) (h : p.all (fun i => decide (Avoids r i))=true) :
 ∀i∈p,Avoids r i:=by
 intro i hi
 exact of_decide_eq_true ((List.all_eq_true.mp h) i hi)
lemma runs_keep {p:Program} {n r ticks:ℕ} {x:Fin n→ℂ} {s u:State}
 (code:∀i∈p,Avoids r i) (run:Runs p n x s ticks u) : u.natReg r=s.natReg r:=by
 induction run with
 | refl=>rfl
 | next step tail ih=>exact ih.trans (step_keep _ _ _ _ _ _ code step)
lemma boundedRuns_keep {p:Program} {n B r ticks:ℕ} {x:Fin n→ℂ} {s u:State}
 (code:∀i∈p,Avoids r i) (run:BoundedRuns p n x B s ticks u) : u.natReg r=s.natReg r:=
 runs_keep code run.runs
lemma executes_keep {p:Program} {n r ticks:ℕ} {x:Fin n→ℂ} {s u:State}
 (code:∀i∈p,Avoids r i) (run:Executes p n x s ticks u) : u.natReg r=s.natReg r:=by
 induction run with
 | halt=>rfl
 | next step tail ih=>exact ih.trans (step_keep _ _ _ _ _ _ code step)
lemma boundedExecution_keep {p:Program} {n B r ticks:ℕ} {x:Fin n→ℂ} {s u:State}
 (code:∀i∈p,Avoids r i) (run:BoundedExecution p n x B s ticks u) : u.natReg r=s.natReg r:=
 executes_keep code run.executes
end ExactFourierCircuits.UniformRecursiveRegisterFrames

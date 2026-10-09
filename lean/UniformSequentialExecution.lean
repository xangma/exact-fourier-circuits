import UniformSequentialAssembly

set_option autoImplicit false
namespace ExactFourierCircuits.UniformSequentialExecution
open UniformMachine UniformAssembly UniformSequentialAssembly UniformBoundedAssembly
noncomputable section

/-- Actual executions of the local helpers, with each helper's charged halt.
This is only a composition predicate; each caller must construct every run. -/
inductive LocalStages (n B:ℕ)(x:Fin n→ℂ):List Program→State→ℕ→State→Prop where
 | nil (s:State)(bound:WordBound B s):LocalStages n B x [] s 0 s
 | cons {p:Program}{ps:List Program}{s v u:State}{t dt:ℕ}
   (head:BoundedExecution p n x B {s with pc:=0} t v)
   (tail:LocalStages n B x ps v dt u):LocalStages n B x (p::ps) s (t+dt) u

def Contains (q:Program)(base:ℕ)(ps:List Program):Prop:=
 ∀before p after,ps=before++p::after→
 CodeAt p q (base+size before) (base+size before+p.length)

lemma program_contains(ps:List Program):Contains (program ps) 0 ps:=by
 intro before p after eq
 subst ps
 simpa only[Nat.zero_add] using stage_code before p after

lemma contains_tail{q:Program}{base:ℕ}{p:Program}{ps:List Program}
 (h:Contains q base (p::ps)):Contains q (base+p.length) ps:=by
 intro before v after eq
 have hv:=h (p::before) v after (by simp only[List.cons_append];rw[eq])
 simpa only[size,Nat.add_assoc] using hv

lemma contains_suffix{q:Program}{base:ℕ}{before ps:List Program}
 (h:Contains q base (before++ps)):Contains q (base+size before) ps:=by
 intro lead p after eq
 have hv:=h (before++lead) p after (by rw[eq];simp only[List.append_assoc])
 simpa only[size_append,Nat.add_assoc] using hv

lemma LocalStages.append{n B t dt:ℕ}{x:Fin n→ℂ}{ps qs:List Program}{s v u:State}
 (a:LocalStages n B x ps s t v)(b:LocalStages n B x qs v dt u):
 LocalStages n B x (ps++qs) s (t+dt) u:=by
 induction a with
 | nil _ _=>simpa only[List.nil_append,Nat.zero_add] using b
 | cons head tail ih=>
  simpa only[List.cons_append,Nat.add_assoc] using LocalStages.cons head (ih b)

/-- Relocation preserves every helper's instruction charge and joins their
states directly. In particular a helper halt is one real continuation jump. -/
theorem LocalStages.runs{n B t:ℕ}{x:Fin n→ℂ}{ps:List Program}{s u:State}
 (h:LocalStages n B x ps s t u){q:Program}{base:ℕ}
 (code:Contains q base ps)(fit:base+size ps≤B):
 BoundedRuns q n x B {s with pc:=base} t {u with pc:=base+size ps}:=by
 induction h generalizing base with
 | nil s wb=>
  simpa only[size,Nat.add_zero] using
   (BoundedRuns.refl (changePC_bound B s base wb (by simpa only[size,Nat.add_zero] using fit)))
 | @cons p ps s v u t dt head tail ih=>
  have first:CodeAt p q base (base+p.length):=by
   simpa only[size,Nat.add_zero,List.nil_append] using code [] p ps rfl
  have bound:base+p.length≤B:=by simp only[size] at fit;omega
  have hr:=boundedExecution_placed first bound bound head
  have tr:=ih (contains_tail code) (by simp only[size] at fit;omega)
  have joined:=hr.trans tr
  simpa only[placed,Nat.add_zero,size,Nat.add_assoc] using joined

/-- The assembled program performs all local executions and its sole final
halt. This theorem supplies no algorithm-specific execution premise. -/
theorem LocalStages.execution{n B t:ℕ}{x:Fin n→ℂ}{ps:List Program}{s u:State}
 (h:LocalStages n B x ps s t u)(fit:size ps≤B):
 BoundedExecution (program ps) n x B {s with pc:=0} (t+1)
 {u with pc:=size ps}:=by
 have run:=h.runs (program_contains ps) (by simpa only[Nat.zero_add] using fit)
 simp only[Nat.zero_add] at run
 have finished:BoundedExecution (program ps) n x B {u with pc:=size ps} 1
  {u with pc:=size ps}:=.halt
   (by simpa only[Nat.zero_add] using run.final_bound)
   (by simp only[step,halt_at])
 simpa only[Nat.zero_add] using run.executes finished

end
end ExactFourierCircuits.UniformSequentialExecution

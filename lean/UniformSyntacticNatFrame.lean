import UniformNewtonTableMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSyntacticNatFrame
open UniformMachine UniformAssembly
noncomputable section

def natDst : Instruction → Option ℕ
 | .natLiteral d _ => some d
 | .length d => some d
 | .natBinary _ d _ _ => some d
 | .loadNat d _ => some d
 | _ => none

def Avoids (p : Program) (j : ℕ) : Prop := ∀ i∈p,natDst i≠some j

lemma relocate_dst (base ret : ℕ) (i : Instruction) :
 natDst (relocate base ret i)=natDst i := by cases i <;> rfl

lemma avoids_map_relocate (p : Program) (base ret j : ℕ) (h:Avoids p j) :
 Avoids (p.map (relocate base ret)) j := by
 intro i hi
 obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hi
 simpa only [relocate_dst] using h a ha

lemma avoids_append (p q : Program) (j : ℕ) (hp:Avoids p j) (hq:Avoids q j) :
 Avoids (p++q) j := by
 intro i hi
 rcases List.mem_append.mp hi with h|h
 · exact hp i h
 · exact hq i h

lemma avoids_flatMap {α : Type*} (ls : List α) (f : α→Program) (j : ℕ)
 (h:∀a∈ls,Avoids (f a) j) : Avoids (ls.flatMap f) j := by
 intro i hi
 obtain ⟨a,ha,hi⟩:=List.mem_flatMap.mp hi
 exact h a ha i hi

lemma avoids_keeps {p : Program} {j : ℕ} (h:Avoids p j) :
 ∀i∈p,UniformNewtonTableMachine.KeepsNat j i := by
 intro i hi
 have hd:=h i hi
 cases i <;> simp only [natDst,UniformNewtonTableMachine.KeepsNat] at hd ⊢
 all_goals exact fun h=>hd (congrArg some h)

theorem step_preserves {p : Program} {n j : ℕ} {x : Fin n→ℂ} {s t : State}
 (safe:Avoids p j) (run:step p n x s=.running t) : t.natReg j=s.natReg j :=
 UniformNewtonTableMachine.step_keeps_nat p n x s t j (avoids_keeps safe) run

lemma runs_preserves {p : Program} {n j ticks : ℕ} {x : Fin n→ℂ} {s t : State}
 (safe:Avoids p j) (run:Runs p n x s ticks t) : t.natReg j=s.natReg j := by
 induction run with
 | refl=>rfl
 | next h _ ih=>exact ih.trans (step_preserves safe h)

lemma boundedRuns_preserves {p : Program} {n B j ticks : ℕ} {x : Fin n→ℂ} {s t : State}
 (safe:Avoids p j) (run:BoundedRuns p n x B s ticks t) : t.natReg j=s.natReg j := by
 induction run with
 | refl=>rfl
 | next _ h _ ih=>exact ih.trans (step_preserves safe h)

lemma execution_preserves {p : Program} {n j ticks : ℕ} {x : Fin n→ℂ} {s t : State}
 (safe:Avoids p j) (run:Executes p n x s ticks t) : t.natReg j=s.natReg j := by
 induction run with
 | halt=>rfl
 | next h _ ih=>exact ih.trans (step_preserves safe h)

lemma boundedExecution_preserves {p : Program} {n B j ticks : ℕ} {x : Fin n→ℂ} {s t : State}
 (safe:Avoids p j) (run:BoundedExecution p n x B s ticks t) : t.natReg j=s.natReg j :=
 execution_preserves safe run.executes
end
end ExactFourierCircuits.UniformSyntacticNatFrame

import UniformLocalCacheContextConductor
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheContextConductor
open UniformMachine UniformNewtonTableMachine

def protectedInstruction:Instruction→Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _=>
  decide (d<100∨106<d) && decide (d<6160∨6179<d)
 | _=>true
lemma context_protected:UniformLocalCacheContextMachine.program.all protectedInstruction=true:=by decide
lemma context_keeps(q:ℕ)(range:(100≤q∧q≤106)∨(6160≤q∧q≤6179)):
 ∀ins∈UniformLocalCacheContextMachine.program,KeepsNat q ins:=by
 intro ins member
 have h:=List.all_eq_true.mp context_protected ins member
 cases ins <;>simp only[protectedInstruction,KeepsNat] at *
 all_goals simp only [Bool.and_eq_true,decide_eq_true_eq] at h
 all_goals omega
lemma program_keeps(q:ℕ)(range:(100≤q∧q≤106)∨(6160≤q∧q≤6179)):
 ∀ins∈program,KeepsNat q ins:=by
 apply UniformReciprocalMachine.keeps_append
 · apply UniformReciprocalMachine.keeps_append
   · exact UniformReciprocalMachine.keeps_relocate q 0 44 (context_keeps q range)
   · exact UniformReciprocalMachine.keeps_relocate q 44 1380
      (UniformLocalCacheSlotConductorMachine.program_keeps q (by rcases range with h|h;exact Or.inl h;exact Or.inr (Or.inl h)))
 · simp [KeepsNat]
lemma execution_nat{B n t:ℕ}{x:Fin n→ℂ}{s u:State}
 (run:BoundedExecution program n x B s t u)(q:ℕ)(range:(100≤q∧q≤106)∨(6160≤q∧q≤6179)):
 u.natReg q=s.natReg q:=UniformNewtonTableMachine.Executes.keeps_nat run.executes (program_keeps q range)
end ExactFourierCircuits.UniformLocalCacheContextConductor

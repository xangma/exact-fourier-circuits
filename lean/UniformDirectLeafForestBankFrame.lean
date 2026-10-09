import UniformDirectLeafForestFrames
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestBankFrame
open UniformMachine
noncomputable section

def free:Instruction→Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _=>decide (d<6400∨6431<d)
 | _=>true
lemma free_relocate(b r:ℕ)(ins:Instruction):free (UniformAssembly.relocate b r ins)=free ins:=by
 cases ins <;>rfl
lemma free_leaf:UniformDirectLeafCacheLeafProgram.program.all free=true:=by
 apply List.all_eq_true.mpr
 intro ins member
 have h:=List.all_eq_true.mp UniformDirectLeafCacheLoopFrames.free_leaf ins member
 cases ins <;>simp_all[free,UniformDirectLeafCacheLoopFrames.free] <;>omega
lemma free_program:UniformDirectLeafForestProgram.program.all free=true:=by
 simp only[UniformDirectLeafForestProgram.program,List.all_append,List.all_map,
  Function.comp_def,free_relocate,free_leaf]
 decide
lemma keeps(q:ℕ)(low:6400≤q)(high:q≤6431):
 ∀ins∈UniformDirectLeafForestProgram.program,UniformNewtonTableMachine.KeepsNat q ins:=by
 intro ins member
 have h:=List.all_eq_true.mp free_program ins member
 cases ins <;>simp_all[free,UniformNewtonTableMachine.KeepsNat] <;>omega
/-- Actual instruction preservation of the physical ordinary workspace bank. -/
theorem execution_bank {n B t:ℕ}{x:Fin n→ℂ}{s u:State}
 (run:BoundedExecution UniformDirectLeafForestProgram.program n x B s t u)
 (q:ℕ)(low:6400≤q)(high:q≤6431):u.natReg q=s.natReg q:=
 UniformNewtonTableMachine.Executes.keeps_nat run.executes (keeps q low high)
end
end ExactFourierCircuits.UniformDirectLeafForestBankFrame

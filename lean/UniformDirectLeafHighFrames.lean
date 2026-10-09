import UniformDirectLeafCacheLoopFrames
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafHighFrames
open UniformMachine
noncomputable section
/-- Supplemental same-bytecode footprint for the genuine forest's node and
orientation controls and the maximum-horizon accumulator. -/
def free:Instruction→Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _=>
  decide (d≠5600 ∧d≠5602 ∧d≠5603 ∧(d<5920∨5925<d))
 | _=>true
lemma free_relocate(b r:ℕ)(ins:Instruction):free (UniformAssembly.relocate b r ins)=free ins:=by
 cases ins <;>rfl
lemma free_body:UniformDirectLeafCacheProgram.program.all free=true:=by
 simp only[UniformDirectLeafCacheProgram.program,List.all_append,List.all_map]
 decide
lemma free_orientations:UniformStoredDirectLeafOrientations.program.all free=true:=by decide
lemma free_loop:UniformDirectLeafCacheLoopProgram.program.all free=true:=by
 simp only[UniformDirectLeafCacheLoopProgram.program,List.all_append,List.all_map,
  Function.comp_def,free_relocate,free_body]
 decide
lemma free_leaf:UniformDirectLeafCacheLeafProgram.program.all free=true:=by
 simp only[UniformDirectLeafCacheLeafProgram.program,List.all_append,List.all_map,
  Function.comp_def,free_relocate,free_loop,free_orientations]
 decide
lemma keeps(q:ℕ)(keep:q=5600∨q=5602∨q=5603∨(5920≤q∧q≤5925)):
 ∀ins∈UniformDirectLeafCacheLeafProgram.program,UniformNewtonTableMachine.KeepsNat q ins:=by
 intro ins member
 have h:=List.all_eq_true.mp free_leaf ins member
 cases ins <;>simp_all[free,UniformNewtonTableMachine.KeepsNat] <;>omega
theorem execution_nat {n B t:ℕ}{x:Fin n→ℂ}{s u:State}
 (run:BoundedExecution UniformDirectLeafCacheLeafProgram.program n x B s t u)
 (q:ℕ)(keep:q=5600∨q=5602∨q=5603∨(5920≤q∧q≤5925)):
 u.natReg q=s.natReg q:=UniformNewtonTableMachine.Executes.keeps_nat run.executes (keeps q keep)
end
end ExactFourierCircuits.UniformDirectLeafHighFrames

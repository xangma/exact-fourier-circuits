import UniformDirectLeafForestExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestFrames
open UniformMachine
noncomputable section

def free:Instruction→Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _=>
  decide ((d<100∨106<d)∧(d<5920∨5925<d)∧d<6700)
 | _=>true
lemma free_relocate(b r:ℕ)(ins:Instruction):free (UniformAssembly.relocate b r ins)=free ins:=by
 cases ins <;>rfl
lemma free_leaf:UniformDirectLeafCacheLeafProgram.program.all free=true:=by
 apply List.all_eq_true.mpr
 intro ins member
 have a:=List.all_eq_true.mp UniformDirectLeafCacheLoopFrames.free_leaf ins member
 have b:=List.all_eq_true.mp UniformDirectLeafCacheLoopFrames.saved_free ins member
 have c:=List.all_eq_true.mp UniformDirectLeafHighFrames.free_leaf ins member
 cases ins <;>simp_all[free,UniformDirectLeafCacheLoopFrames.free,
  UniformDirectLeafCacheLoopFrames.savedFree,UniformDirectLeafHighFrames.free] <;>omega
lemma free_program:UniformDirectLeafForestProgram.program.all free=true:=by
 simp only[UniformDirectLeafForestProgram.program,List.all_append,List.all_map,
  Function.comp_def,free_relocate,free_leaf]
 decide
lemma keeps(q:ℕ)(outside:6700≤q∨(100≤q∧q≤106)∨(5920≤q∧q≤5925)):
 ∀ins∈UniformDirectLeafForestProgram.program,UniformNewtonTableMachine.KeepsNat q ins:=by
 intro ins member
 have h:=List.all_eq_true.mp free_program ins member
 cases ins <;>simp_all[free,UniformNewtonTableMachine.KeepsNat] <;>omega
/-- The actual whole461 code retains saved metadata, the physical maximum
horizon and all allocator/outer-axis registers at6700 and above. -/
theorem execution_nat {n B t:ℕ}{x:Fin n→ℂ}{s u:State}
 (run:BoundedExecution UniformDirectLeafForestProgram.program n x B s t u)
 (q:ℕ)(outside:6700≤q∨(100≤q∧q≤106)∨(5920≤q∧q≤5925)):
 u.natReg q=s.natReg q:=UniformNewtonTableMachine.Executes.keeps_nat run.executes (keeps q outside)
end
end ExactFourierCircuits.UniformDirectLeafForestFrames

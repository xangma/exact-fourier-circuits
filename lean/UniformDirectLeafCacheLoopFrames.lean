import UniformDirectLeafCacheLeafProgram
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheLoopFrames
open UniformMachine
noncomputable section

def free : Instruction→Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _ =>
  decide (d<6100∨(6600≤d∧d<6636)∨(6640≤d∧d<6653))
 | _=>true
lemma free_relocate (b r:ℕ) (ins:Instruction):free (UniformAssembly.relocate b r ins)=free ins:=by
 cases ins <;>rfl
lemma free_body : UniformDirectLeafCacheProgram.program.all free=true:=by
 apply List.all_eq_true.mpr
 intro ins member
 have h:=List.all_eq_true.mp UniformDirectLeafCacheFrames.free_program ins member
 cases ins <;>simp_all[free,UniformDirectLeafCacheFrames.free] <;>omega
lemma free_orientations : UniformStoredDirectLeafOrientations.program.all free=true:=by decide
lemma free_loop : UniformDirectLeafCacheLoopProgram.program.all free=true:=by
 simp only[UniformDirectLeafCacheLoopProgram.program,List.all_append,List.all_map,
  Function.comp_def,free_relocate,free_body]
 decide
lemma free_leaf : UniformDirectLeafCacheLeafProgram.program.all free=true:=by
 simp only[UniformDirectLeafCacheLeafProgram.program,List.all_append,List.all_map,
  Function.comp_def,free_relocate,free_loop,free_orientations]
 decide
lemma keeps {p:Program} (all:p.all free=true) (q:ℕ) (high:6100≤q)
 (outside:(q<6600∨6636≤q)∧(q<6640∨6653≤q)):
 ∀ins∈p,UniformNewtonTableMachine.KeepsNat q ins:=by
 intro ins member
 have h:=List.all_eq_true.mp all ins member
 cases ins <;>simp_all[free,UniformNewtonTableMachine.KeepsNat] <;>omega
/-- Actual instruction footprint, including descriptor production and every
cache iteration: forest registers, future allocator/axis controls are retained. -/
theorem execution_nat {n B t:ℕ} {x:Fin n→ℂ} {s u:State}
 (run:BoundedExecution UniformDirectLeafCacheLeafProgram.program n x B s t u)
 (q:ℕ) (high:6100≤q) (outside:(q<6600∨6636≤q)∧(q<6640∨6653≤q)):
 u.natReg q=s.natReg q:=
 UniformNewtonTableMachine.Executes.keeps_nat run.executes (keeps free_leaf q high outside)

def savedFree : Instruction→Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _ =>decide (d<100∨106<d)
 | _=>true
lemma saved_relocate (b r:ℕ) (ins:Instruction):savedFree (UniformAssembly.relocate b r ins)=savedFree ins:=by
 cases ins <;>rfl
lemma saved_body : UniformDirectLeafCacheProgram.program.all savedFree=true:=UniformDirectLeafCacheFrames.saved_free
lemma saved_orientations : UniformStoredDirectLeafOrientations.program.all savedFree=true:=by decide
lemma saved_loop : UniformDirectLeafCacheLoopProgram.program.all savedFree=true:=by
 simp only[UniformDirectLeafCacheLoopProgram.program,List.all_append,List.all_map,
  Function.comp_def,saved_relocate,saved_body]
 decide
lemma saved_free : UniformDirectLeafCacheLeafProgram.program.all savedFree=true:=by
 simp only[UniformDirectLeafCacheLeafProgram.program,List.all_append,List.all_map,
  Function.comp_def,saved_relocate,saved_loop,saved_orientations]
 decide
lemma keeps_saved (q:ℕ) (lo:100≤q) (hi:q≤106):
 ∀ins∈UniformDirectLeafCacheLeafProgram.program,UniformNewtonTableMachine.KeepsNat q ins:=by
 intro ins member
 have h:=List.all_eq_true.mp saved_free ins member
 cases ins <;>simp_all[savedFree,UniformNewtonTableMachine.KeepsNat] <;>omega
theorem execution_saved {n B t:ℕ} {x:Fin n→ℂ} {s u:State}
 (run:BoundedExecution UniformDirectLeafCacheLeafProgram.program n x B s t u)
 (q:ℕ) (lo:100≤q) (hi:q≤106):u.natReg q=s.natReg q:=
 UniformNewtonTableMachine.Executes.keeps_nat run.executes (keeps_saved q lo hi)
end
end ExactFourierCircuits.UniformDirectLeafCacheLoopFrames

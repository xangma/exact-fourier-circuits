import UniformDirectLeafCacheRetained
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheFrames
open UniformMachine UniformDirectLeafCacheProgram
noncomputable section

def free : Instruction→Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _ =>
  decide (d<6100∨(6640≤d∧d<6653))
 | _=>true
lemma free_program : program.all free=true := by
 simp only[program,List.all_append,List.all_map]
 decide
lemma keeps (q:ℕ) (high:6100≤q) (outside:q<6640∨6653≤q) :
 ∀ins∈program,UniformNewtonTableMachine.KeepsNat q ins := by
 intro ins member
 have h:=List.all_eq_true.mp free_program ins member
 cases ins <;>simp_all[free,UniformNewtonTableMachine.KeepsNat] <;>omega
/-- The complete actual264 instruction census preserves high cache-loop
controls, ordinary caller headers and every saved global header. -/
theorem execution_nat {n B t:ℕ} {x:Fin n→ℂ} {s u:State}
 (run:BoundedExecution program n x B s t u) (q:ℕ) (high:6100≤q) (outside:q<6640∨6653≤q) :
 u.natReg q=s.natReg q := UniformNewtonTableMachine.Executes.keeps_nat run.executes (keeps q high outside)

def savedFree : Instruction→Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _ =>decide (d<100∨106<d)
 | _=>true
lemma saved_free : program.all savedFree=true := by
 simp only[program,List.all_append,List.all_map]
 decide
lemma keeps_saved (q:ℕ) (lo:100≤q) (hi:q≤106) :
 ∀ins∈program,UniformNewtonTableMachine.KeepsNat q ins := by
 intro ins member
 have h:=List.all_eq_true.mp saved_free ins member
 cases ins <;>simp_all[savedFree,UniformNewtonTableMachine.KeepsNat] <;>omega
theorem execution_saved {n B t:ℕ} {x:Fin n→ℂ} {s u:State}
 (run:BoundedExecution program n x B s t u) (q:ℕ) (lo:100≤q) (hi:q≤106) :
 u.natReg q=s.natReg q := UniformNewtonTableMachine.Executes.keeps_nat run.executes (keeps_saved q lo hi)
end
end ExactFourierCircuits.UniformDirectLeafCacheFrames

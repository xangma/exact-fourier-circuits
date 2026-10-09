import UniformLocalMatchingSlotDirectory
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalMatchingSlotDirectory
open UniformMachine UniformAssembly
noncomputable section

def driverFree : Instruction → Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _ => decide (d < 6100)
 | _ => true
/-- Complete literal80 instruction census, including MatchingAxis55 and all
15 ABI publication instructions. No giant common-program bytecode unfolds. -/
lemma driver_free:program.all driverFree=true:=by decide
lemma driver_keeps (q:ℕ) (hq:6100≤q):
 ∀ins∈program,UniformNewtonTableMachine.KeepsNat q ins:=by
 intro ins member
 have free:=List.all_eq_true.mp driver_free ins member
 cases ins <;>simp_all[driverFree,UniformNewtonTableMachine.KeepsNat] <;>omega

/-- Actual80 retains every high driver register, not just a chosen finite
set. This supplements the frozen execution's scalar and prefix-heap frames. -/
theorem execution_keeps_driver {n B ticks:ℕ} {x:Fin n→ℂ} {s u:State}
 (run:BoundedExecution program n x B s ticks u):
 ∀q,6100≤q→u.natReg q=s.natReg q:=by
 intro q high
 exact UniformNewtonTableMachine.Executes.keeps_nat run.executes (driver_keeps q high)
end
end ExactFourierCircuits.UniformLocalMatchingSlotDirectory

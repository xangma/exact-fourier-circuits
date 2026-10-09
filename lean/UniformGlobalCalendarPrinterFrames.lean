import UniformGlobalCalendarUnionRowsTable
import UniformGlobalCalendarFactorMergeTable
import UniformNewtonTableMachine

set_option autoImplicit false

namespace ExactFourierCircuits.UniformGlobalCalendarPrinterFrames
open UniformMachine

def Destinations (i : Instruction) : Prop := match i with
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _ => 6743 ≤ d ∧ d < 6753
 | _ => True
instance (i : Instruction) : Decidable (Destinations i) := by cases i <;> simp [Destinations] <;> infer_instance

lemma rows_destinations : ∀ i ∈ UniformGlobalCalendarUnionRows.program, Destinations i := by
 have all : UniformGlobalCalendarUnionRows.program.all (fun i => decide (Destinations i)) = true := by decide
 exact fun i hi => of_decide_eq_true ((List.all_eq_true.mp all) i hi)
lemma factor_destinations : ∀ i ∈ UniformGlobalCalendarFactorMerge.program, Destinations i := by
 have all : UniformGlobalCalendarFactorMerge.program.all (fun i => decide (Destinations i)) = true := by decide
 exact fun i hi => of_decide_eq_true ((List.all_eq_true.mp all) i hi)

lemma keeps_nat (p : Program) (safe : ∀ i ∈ p, Destinations i) (q : ℕ) (hq : q<6743 ∨ 6753 ≤ q) :
 ∀ i ∈ p, UniformNewtonTableMachine.KeepsNat q i := by
 intro i hi
 have bounds := safe i hi
 cases i <;> simp only [Destinations,UniformNewtonTableMachine.KeepsNat] at bounds ⊢ <;> omega

/-- All outer calendar counters and descriptors survive the actual row printer. -/
theorem rows_natFrame {n B ticks : ℕ} {x : Fin n → ℂ} {s u : State}
 (run : BoundedExecution UniformGlobalCalendarUnionRows.program n x B s ticks u)
 (q : ℕ) (hq : q<6743 ∨ 6753 ≤ q) : u.natReg q=s.natReg q :=
 UniformNewtonTableMachine.Executes.keeps_nat run.executes
  (keeps_nat _ rows_destinations q hq)

/-- All outer calendar counters and descriptors survive the actual lane merger. -/
theorem factor_natFrame {n B ticks : ℕ} {x : Fin n → ℂ} {s u : State}
 (run : BoundedExecution UniformGlobalCalendarFactorMerge.program n x B s ticks u)
 (q : ℕ) (hq : q<6743 ∨ 6753 ≤ q) : u.natReg q=s.natReg q :=
 UniformNewtonTableMachine.Executes.keeps_nat run.executes
  (keeps_nat _ factor_destinations q hq)

end ExactFourierCircuits.UniformGlobalCalendarPrinterFrames

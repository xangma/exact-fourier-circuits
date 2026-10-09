import UniformLocalCacheSlotExecutionLoop

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheSlotConductorMachine
open UniformMachine UniformTensorMonomialMachine
open UniformNewtonTableMachine (KeepsNat)

def protectedInstruction:Instruction → Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _ =>
  decide (d < 100 ∨ 106 < d) && decide (d < 6160 ∨ 6179 < d) && decide (d≠6200)
 | _=>true
lemma header_protected:H.program.all protectedInstruction=true:=by decide
lemma directory_protected:D.program.all protectedInstruction=true:=by decide
lemma boot_protected:(C.boot.map Op.code).all protectedInstruction=true:=by decide
lemma advance_protected:(C.advance.map Op.code).all protectedInstruction=true:=by decide
lemma protected_keeps {p:Program} (h:p.all protectedInstruction=true) (q:ℕ)
 (range:(100 ≤ q ∧q ≤ 106) ∨ (6160 ≤ q ∧q ≤ 6179) ∨ q=6200):
 ∀ins∈p,KeepsNat q ins:=by
 intro ins member
 have hi:=List.all_eq_true.mp h ins member
 cases ins <;>simp only [protectedInstruction,KeepsNat] at *
 all_goals simp only [Bool.and_eq_true,decide_eq_true_eq] at hi
 all_goals omega

/-- The actual fixed loop preserves saved global metadata and its own outer
request-driver registers. This is a syntactic footprint, not an entry premise. -/
lemma program_keeps (q:ℕ)
 (range:(100 ≤ q ∧q ≤ 106) ∨ (6160 ≤ q ∧q ≤ 6179) ∨ q=6200):∀ins∈program,KeepsNat q ins:=by
 have boot:=protected_keeps boot_protected q range
 have branch:∀ins∈([.branchLT 6140 6141 15 1335]:Program),KeepsNat q ins:=by simp [KeepsNat]
 have header:=UniformReciprocalMachine.keeps_relocate q 15 89 (protected_keeps header_protected q range)
 have factor:=UniformReciprocalMachine.keeps_relocate q 89 1245
  (UniformLocalFactorDispatchMachine.program_keeps q (by omega) (by omega) (by omega) (by intros;omega))
 have directory:=UniformReciprocalMachine.keeps_relocate q 1245 1325 (protected_keeps directory_protected q range)
 have advance:=protected_keeps advance_protected q range
 have halt:∀ins∈([.jump 14,.halt]:Program),KeepsNat q ins:=by simp [KeepsNat]
 exact UniformReciprocalMachine.keeps_append q
  (UniformReciprocalMachine.keeps_append q
   (UniformReciprocalMachine.keeps_append q
    (UniformReciprocalMachine.keeps_append q
     (UniformReciprocalMachine.keeps_append q (UniformReciprocalMachine.keeps_append q boot branch) header) factor) directory) advance) halt

lemma runs_keeps {p:Program} {B n t:ℕ} {x:Fin n → ℂ} {s u:State}
 (run:BoundedRuns p n x B s t u) (q:ℕ) (keeps:∀ins∈p,KeepsNat q ins):u.natReg q=s.natReg q:=by
 induction run with
 | refl=>rfl
 | next wb step tail ih=>exact ih.trans (UniformNewtonTableMachine.step_keeps_nat p n x _ _ q keeps step)

lemma execution_nat {B n t:ℕ} {x:Fin n → ℂ} {s u:State}
 (run:BoundedExecution program n x B s t u) (q:ℕ)
 (range:(100 ≤ q ∧q ≤ 106) ∨ (6160 ≤ q ∧q ≤ 6179) ∨ q=6200):u.natReg q=s.natReg q:=
 UniformNewtonTableMachine.Executes.keeps_nat run.executes (program_keeps q range)

end ExactFourierCircuits.UniformLocalCacheSlotConductorMachine

import UniformLocalRectanglePhaseBanks

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalRectanglePhaseBanks
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformNewtonTableMachine (KeepsNat)

def driverProtected:Instruction → Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _ =>decide (d<4237)
 | _=>true
lemma height_protected:UniformCrossHeightPreparationMachine.program.all driverProtected=true:=by decide

lemma height_keeps(q:ℕ)(high:4237≤q):
 ∀ins∈UniformCrossHeightPreparationMachine.program,KeepsNat q ins:=by
 intro ins member
 have guard:=List.all_eq_true.mp height_protected ins member
 cases ins <;>simp only [driverProtected,KeepsNat] at *
 all_goals first | trivial | simp only [decide_eq_true_eq] at guard;omega

lemma disabled_keeps(q:ℕ)(high:4237≤q):∀ins∈H.program,KeepsNat q ins:=by
 intro ins member
 simp only [H.program,UniformLocalDisabledHeightMachine.program,List.mem_append,
  List.mem_map,List.mem_singleton] at member
 rcases member with (⟨o,ho,rfl⟩|⟨i,hi,rfl⟩)|rfl
 · simp only [UniformLocalDisabledHeightMachine.setup,List.mem_cons,List.not_mem_nil,or_false] at ho
   rcases ho with rfl|rfl|rfl|rfl|rfl|rfl
   all_goals simp only [Op.code,KeepsNat];omega
 · exact UniformReciprocalMachine.keeps_relocate q 6 192 (height_keeps q high) _
    (List.mem_map.mpr ⟨i,hi,rfl⟩)
 · trivial

/-- The genuine2308 producer leaves all outer cache-driver and concrete
workspace-address registers unchanged. No preserved-register premise is used. -/
lemma program_keeps_driver(q:ℕ)(high:4237≤q):∀ins∈program,KeepsNat q ins:=by
 exact UniformReciprocalMachine.keeps_append q
  (UniformReciprocalMachine.keeps_append q
   (UniformReciprocalMachine.keeps_relocate q 0 2114 (replay_keeps q (by omega)))
   (UniformReciprocalMachine.keeps_relocate q 2114 2307 (disabled_keeps q high)))
  (by simp [KeepsNat])

lemma execution_keeps_driver {n B t:ℕ}{x:Fin n → ℂ}{s u:State}
 (run:BoundedExecution program n x B s t u)(q:ℕ)(high:4237≤q):u.natReg q=s.natReg q:=
 UniformNewtonTableMachine.Executes.keeps_nat run.executes (program_keeps_driver q high)

end ExactFourierCircuits.UniformLocalRectanglePhaseBanks

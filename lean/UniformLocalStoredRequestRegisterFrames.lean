import UniformLocalStoredRequestExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalStoredRequestRegisterFrames
open UniformMachine UniformNewtonTableMachine UniformAssembly UniformTensorMonomialMachine

def clockInstruction:Instruction → Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _=>decide (d < 5920 ∨ 5925 < d)
 | _=>true
lemma clock_keeps {p:Program}(h:p.all clockInstruction=true)(q:ℕ)(lo:5920 ≤ q)(hi:q ≤ 5925):
 ∀ins∈p,KeepsNat q ins:=by
 intro ins mem
 have h:=List.all_eq_true.mp h ins mem
 cases ins <;>simp only[clockInstruction,KeepsNat] at *
 all_goals simp only[decide_eq_true_eq] at h
 all_goals omega

namespace S
open UniformLocalCacheSlotConductorMachine
lemma header:H.program.all clockInstruction=true:=by decide
lemma directory:D.program.all clockInstruction=true:=by decide
lemma boot:(C.boot.map UniformTensorMonomialMachine.Op.code).all clockInstruction=true:=by decide
lemma advance:(C.advance.map UniformTensorMonomialMachine.Op.code).all clockInstruction=true:=by decide
lemma keeps(q:ℕ)(lo:5920 ≤ q)(hi:q ≤ 5925):∀ins∈UniformLocalCacheSlotConductorMachine.program,KeepsNat q ins:=by
 have a:=clock_keeps boot q lo hi
 have b:∀ins∈([.branchLT 6140 6141 15 1335]:Program),KeepsNat q ins:=by simp[KeepsNat]
 have c:=UniformReciprocalMachine.keeps_relocate q 15 89 (clock_keeps header q lo hi)
 have d:=UniformReciprocalMachine.keeps_relocate q 89 1245
  (UniformLocalFactorDispatchMachine.program_keeps q (Or.inr (by omega)) (by omega) (by omega) (by intros;omega))
 have e:=UniformReciprocalMachine.keeps_relocate q 1245 1325 (clock_keeps directory q lo hi)
 have f:=clock_keeps advance q lo hi
 have g:∀ins∈([.jump 14,.halt]:Program),KeepsNat q ins:=by simp[KeepsNat]
 exact UniformReciprocalMachine.keeps_append q
  (UniformReciprocalMachine.keeps_append q
   (UniformReciprocalMachine.keeps_append q
    (UniformReciprocalMachine.keeps_append q
     (UniformReciprocalMachine.keeps_append q (UniformReciprocalMachine.keeps_append q a b) c) d) e) f) g
end S

lemma contextClock:UniformLocalCacheContextMachine.program.all clockInstruction=true:=by decide
lemma context_keeps(q:ℕ)(lo:5920 ≤ q)(hi:q ≤ 5925):
 ∀ins∈UniformLocalCacheContextConductor.program,KeepsNat q ins:=by
 apply UniformReciprocalMachine.keeps_append
 · apply UniformReciprocalMachine.keeps_append
   · exact UniformReciprocalMachine.keeps_relocate q 0 44 (clock_keeps contextClock q lo hi)
   · exact UniformReciprocalMachine.keeps_relocate q 44 1380 (S.keeps q lo hi)
 · simp[KeepsNat]

lemma rectangle_keeps(q:ℕ)(lo:5920 ≤ q)(hi:q ≤ 5925):
 ∀ins∈UniformLocalRectangleCachePreparation.program,KeepsNat q ins:=by
 apply UniformReciprocalMachine.keeps_append
 · apply UniformReciprocalMachine.keeps_append
   · exact UniformReciprocalMachine.keeps_relocate q 0 2308
      (UniformLocalRectanglePhaseBanks.program_keeps_driver q (by omega))
   · exact UniformReciprocalMachine.keeps_relocate q 2308 3689 (context_keeps q lo hi)
 · simp[KeepsNat]

lemma storedClock:UniformLocalStoredRequestBootstrap.program.all clockInstruction=true:=by decide
lemma stored_keeps(q:ℕ)(lo:5920 ≤ q)(hi:q ≤ 5925):
 ∀ins∈UniformLocalStoredRectanglePreparation.program,KeepsNat q ins:=by
 apply UniformReciprocalMachine.keeps_append
 · apply UniformReciprocalMachine.keeps_append
   · exact UniformReciprocalMachine.keeps_relocate q 0 47 (clock_keeps storedClock q lo hi)
   · exact UniformReciprocalMachine.keeps_relocate q 47 3737 (rectangle_keeps q lo hi)
 · simp[KeepsNat]

lemma cursorClock:UniformLocalRequestCursorMachine.program.all clockInstruction=true:=by decide
lemma advanceClock:UniformLocalRequestAdvanceMachine.program.all clockInstruction=true:=by decide
lemma program_keeps(q:ℕ)(lo:5920 ≤ q)(hi:q ≤ 5925):
 ∀ins∈UniformLocalStoredRequestLoop.program,KeepsNat q ins:=by
 have first:∀ins∈UniformLocalStoredRequestLoop.beforeCache,KeepsNat q ins:=by
  apply UniformReciprocalMachine.keeps_append
  · exact UniformReciprocalMachine.keeps_relocate q 0 21 (clock_keeps cursorClock q lo hi)
  · intro ins mem
    simp only[List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl <;>simp only[KeepsNat] <;>omega
 have second:∀ins∈UniformLocalStoredRequestLoop.beforeAdvance,KeepsNat q ins:=
  UniformReciprocalMachine.keeps_append q first
   (UniformReciprocalMachine.keeps_relocate q 24 3762 (stored_keeps q lo hi))
 exact UniformReciprocalMachine.keeps_append q
  (UniformReciprocalMachine.keeps_append q second
   (UniformReciprocalMachine.keeps_relocate q 3762 21 (clock_keeps advanceClock q lo hi)))
  (by simp[KeepsNat])

lemma execution_clock {n B ticks:ℕ}{x:Fin n → ℂ}{s u:State}
 (run:BoundedExecution UniformLocalStoredRequestLoop.program n x B s ticks u)
 (q:ℕ)(lo:5920 ≤ q)(hi:q ≤ 5925):u.natReg q=s.natReg q:=
 Executes.keeps_nat run.executes (program_keeps q lo hi)

end ExactFourierCircuits.UniformLocalStoredRequestRegisterFrames

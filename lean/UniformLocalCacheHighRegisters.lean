import UniformLocalCacheContextFrames
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheSlotConductorMachine
open UniformMachine UniformNewtonTableMachine UniformTensorMonomialMachine

def belowHigh:Instruction→Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _=>decide (d<6400)
 | _=>true
lemma high_header:H.program.all belowHigh=true:=by decide
lemma high_directory:D.program.all belowHigh=true:=by decide
lemma high_boot:(C.boot.map UniformTensorMonomialMachine.Op.code).all belowHigh=true:=by decide
lemma high_advance:(C.advance.map UniformTensorMonomialMachine.Op.code).all belowHigh=true:=by decide
lemma below_high_keeps {p:Program}(h:p.all belowHigh=true)(q:ℕ)(lo:6400≤q):∀ins∈p,KeepsNat q ins:=by
 intro ins mem
 have h:=List.all_eq_true.mp h ins mem
 cases ins <;>simp only [belowHigh,KeepsNat] at *
 all_goals simp only [decide_eq_true_eq] at h
 all_goals omega
lemma program_keeps_high(q:ℕ)(lo:6400≤q):∀ins∈program,KeepsNat q ins:=by
 have boot:=below_high_keeps high_boot q lo
 have branch:∀ins∈([.branchLT 6140 6141 15 1335]:Program),KeepsNat q ins:=by simp[KeepsNat]
 have header:=UniformReciprocalMachine.keeps_relocate q 15 89 (below_high_keeps high_header q lo)
 have factors:=UniformReciprocalMachine.keeps_relocate q 89 1245
  (UniformLocalFactorDispatchMachine.program_keeps q (Or.inr (by omega)) (by omega) (by omega) (by intros;omega))
 have directory:=UniformReciprocalMachine.keeps_relocate q 1245 1325 (below_high_keeps high_directory q lo)
 have advance:=below_high_keeps high_advance q lo
 have halt:∀ins∈([.jump 14,.halt]:Program),KeepsNat q ins:=by simp[KeepsNat]
 exact UniformReciprocalMachine.keeps_append q
  (UniformReciprocalMachine.keeps_append q
   (UniformReciprocalMachine.keeps_append q
    (UniformReciprocalMachine.keeps_append q
     (UniformReciprocalMachine.keeps_append q (UniformReciprocalMachine.keeps_append q boot branch) header) factors) directory) advance) halt
end ExactFourierCircuits.UniformLocalCacheSlotConductorMachine

namespace ExactFourierCircuits.UniformLocalCacheContextConductor
open UniformMachine UniformNewtonTableMachine
lemma high_context:UniformLocalCacheContextMachine.program.all UniformLocalCacheSlotConductorMachine.belowHigh=true:=by decide
lemma program_keeps_high(q:ℕ)(lo:6400≤q):∀ins∈program,KeepsNat q ins:=by
 apply UniformReciprocalMachine.keeps_append
 · apply UniformReciprocalMachine.keeps_append
   · exact UniformReciprocalMachine.keeps_relocate q 0 44
      (UniformLocalCacheSlotConductorMachine.below_high_keeps high_context q lo)
   · exact UniformReciprocalMachine.keeps_relocate q 44 1380
      (UniformLocalCacheSlotConductorMachine.program_keeps_high q lo)
 · simp[KeepsNat]
lemma execution_nat_high{B n t:ℕ}{x:Fin n→ℂ}{s u:State}
 (run:BoundedExecution program n x B s t u)(q:ℕ)(lo:6400≤q):u.natReg q=s.natReg q:=
 UniformNewtonTableMachine.Executes.keeps_nat run.executes (program_keeps_high q lo)
end ExactFourierCircuits.UniformLocalCacheContextConductor

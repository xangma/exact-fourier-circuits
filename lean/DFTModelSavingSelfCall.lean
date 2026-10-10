import DFTModelSavingControl
import UniformRecursiveSavingExecution

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingSelfCall
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine
namespace P
export DFTModelSavingProgram (ordinary body large program)
end P
noncomputable section
attribute [local irreducible] P.ordinary P.body P.large P.program

def evaluate (fuel : ℕ) : Handler ChildPort :=
  depthRun (P.ordinary.run ()) P.body.run fuel

lemma zero_value (k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    (evaluate 0 ((k,I),v)).val=(run P.ordinary ((k,I),v)).val := rfl
lemma succ_value (fuel k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    (evaluate (fuel+1) ((k,I),v)).val=(P.body.run (evaluate fuel) ((k,I),v)).val := rfl

/-- The actual exponent controls calls through runtime seed/unit headers.
The upstream fuel counter merely bounds recursion; any fuel at least k has
exactly the same complete Tagged result, including both affine channels. -/
theorem fuel_stable (k : ℕ) : ∀fuel:ℕ,k≤fuel→∀I:ℂ,∀v:Tape Tagged.T,
    (evaluate fuel ((k,I),v)).val=(evaluate k ((k,I),v)).val := by
  induction k using Nat.strong_induction_on with
  | h k ih=>
    intro fuel enough I v
    by_cases small:k<UniformRecursiveSavingProgram.threshold
    · have base : ∀f:ℕ,(evaluate f ((k,I),v)).val=(run P.ordinary ((k,I),v)).val := by
        intro f
        cases f with
        | zero=>exact zero_value k I v
        | succ f=>rw [succ_value,DFTModelSavingControl.body_value,ite_eq_left small]
      exact (base fuel).trans (base k).symm
    · have large:UniformRecursiveSavingProgram.threshold≤k:=by omega
      have geometry:=UniformRecursiveSavingExecution.recursive_geometry k large
      have qlt:k/UniformFixedNetwork.m<k:=geometry.2.1
      have kpos:0<k:=lt_of_le_of_lt (Nat.zero_le _) qlt
      have fpos:0<fuel:=lt_of_lt_of_le kpos enough
      obtain ⟨k',rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt kpos)
      obtain ⟨f',rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt fpos)
      rw [succ_value,succ_value,DFTModelSavingControl.body_value,
        DFTModelSavingControl.body_value,ite_eq_right small,ite_eq_right small]
      apply DFTModelSavingControl.large_value_congr
      intro J bank
      exact (ih _ qlt f' (by omega) J bank).trans (ih _ qlt k' (by omega) J bank).symm

/-- No callback is supplied: the handler in this equation is the SAME closed
program. Each internal call carries q=k/m and the single returned tape keeps
both baseline and homogeneous coordinates. -/
theorem recursive_value (k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    (run P.program ((k,I),v)).val=
      if k<UniformRecursiveSavingProgram.threshold then (run P.ordinary ((k,I),v)).val
      else (P.large.run (run P.program) ((k,I),v)).val := by
  rw [DFTModelSavingProgram.program_run]
  change (evaluate k ((k,I),v)).val=_
  by_cases small:k<UniformRecursiveSavingProgram.threshold
  · rw [ite_eq_left small]
    cases k with
    | zero=>rfl
    | succ k=>rw [succ_value,DFTModelSavingControl.body_value,ite_eq_left small]
  · rw [ite_eq_right small]
    have large:UniformRecursiveSavingProgram.threshold≤k:=by omega
    have qlt:k/UniformFixedNetwork.m<k:=
      (UniformRecursiveSavingExecution.recursive_geometry k large).2.1
    have kpos:0<k:=lt_of_le_of_lt (Nat.zero_le _) qlt
    obtain ⟨k',rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt kpos)
    rw [succ_value,DFTModelSavingControl.body_value,ite_eq_right small]
    apply DFTModelSavingControl.large_value_congr
    intro J bank
    rw [DFTModelSavingProgram.program_run]
    exact fuel_stable _ k' (by omega) J bank

end
end ExactFourierCircuits.DFTModelSavingSelfCall

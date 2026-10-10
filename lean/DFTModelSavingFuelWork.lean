import DFTModelSavingLargeWorkCongruence
import DFTModelSavingSelfCall

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingSelfCall
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine DFTModelSavingBillCongruence
open DFTModelSavingWorkCongruence
noncomputable section
attribute [local irreducible] P.ordinary P.body P.large P.program

lemma evaluate_succ (fuel k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    evaluate (fuel+1) ((k,I),v)=(P.body.run (evaluate fuel) ((k,I),v)).pay 1 (fuel+1) := rfl

/-- For positive exponents sufficient fuel changes peak only. The exact
charged work and both paired channels agree. Large calls always have q≥1. -/
theorem fuel_related (k : ℕ) (positive : 0<k) : ∀fuel:ℕ,k≤fuel→∀I:ℂ,∀v:Tape Tagged.T,
    Related (evaluate fuel ((k,I),v)) (evaluate k ((k,I),v)) := by
  induction k using Nat.strong_induction_on with
  | h k ih=>
    intro fuel enough I v
    have fpos:0<fuel:=lt_of_lt_of_le positive enough
    obtain ⟨k',rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
    obtain ⟨f',rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt fpos)
    by_cases small:k'+1<UniformRecursiveSavingProgram.threshold
    · rw [evaluate_succ,evaluate_succ,DFTModelSavingCost.body_run,
        DFTModelSavingCost.body_run,ite_eq_left small,ite_eq_left small]
      constructor
      · rfl
      · rfl
    · have large:UniformRecursiveSavingProgram.threshold≤k'+1:=by omega
      have geometry:=UniformRecursiveSavingExecution.recursive_geometry (k'+1) large
      have qlt:(k'+1)/UniformFixedNetwork.m<k'+1:=geometry.2.1
      have qp:0<(k'+1)/UniformFixedNetwork.m:=geometry.1
      rw [evaluate_succ,evaluate_succ,DFTModelSavingCost.body_run,
        DFTModelSavingCost.body_run,ite_eq_right small,ite_eq_right small]
      have same : HandlerRelated ((k'+1)/UniformFixedNetwork.m) (evaluate f') (evaluate k') := by
        intro J bank
        have a:=ih _ qlt qp f' (by omega) J bank
        have b:=ih _ qlt qp k' (by omega) J bank
        exact ⟨a.1.trans b.1.symm,a.2.trans b.2.symm⟩
      have out:=large_related (evaluate f') (evaluate k') (k'+1) I v same
      exact ⟨out.1,congrArg (fun w=>w+9+1) out.2⟩

/-- A real internal child handler has the same exact result as the closed
program and no more work. The closed entry has seven extra work steps. -/
theorem fuel_closed (k fuel : ℕ) (positive : 0<k) (enough : k≤fuel)
    (I : ℂ) (v : Tape Tagged.T) :
    (evaluate fuel ((k,I),v)).val=(run P.program ((k,I),v)).val ∧
    (evaluate fuel ((k,I),v)).work≤(run P.program ((k,I),v)).work := by
  have same:=fuel_related k positive fuel enough I v
  rw [DFTModelSavingProgram.program_run]
  refine ⟨same.1,?_⟩
  change _≤(evaluate k ((k,I),v)).work+7
  rw [same.2]
  omega

/-- The zero-exponent base may use three more steps at positive fuel. This
constant is paid by the actual recursive call/return overhead. -/
theorem fuel_closed_all (k fuel : ℕ) (enough : k≤fuel)
    (I : ℂ) (v : Tape Tagged.T) :
    (evaluate fuel ((k,I),v)).val=(run P.program ((k,I),v)).val ∧
    (evaluate fuel ((k,I),v)).work≤(run P.program ((k,I),v)).work+3 := by
  by_cases positive:0<k
  · have h:=fuel_closed k fuel positive enough I v
    exact ⟨h.1,h.2.trans (Nat.le_add_right _ _)⟩
  · have zero:k=0:=by omega
    subst k
    have val : (evaluate fuel ((0,I),v)).val=(run P.program ((0,I),v)).val := by
      rw [DFTModelSavingProgram.program_run]
      exact fuel_stable 0 fuel (Nat.zero_le _) I v
    refine ⟨val,?_⟩
    rw [DFTModelSavingProgram.program_run]
    have small:0<UniformRecursiveSavingProgram.threshold:=by decide
    cases fuel with
    | zero=>change (run P.ordinary ((0,I),v)).work+1≤(run P.ordinary ((0,I),v)).work+1+7+3;omega
    | succ fuel=>
      rw [evaluate_succ,DFTModelSavingCost.body_run,ite_eq_left small]
      change (run P.ordinary ((0,I),v)).work+1+9+1≤(run P.ordinary ((0,I),v)).work+1+7+3
      omega

end
end ExactFourierCircuits.DFTModelSavingSelfCall

import DFTModelSavingPeakLarge
import UniformRecursiveSavingExecution

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingPeak
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine DFTModelSavingResidualBoolean UniformFixedNetwork
noncomputable section
namespace P
export DFTModelSavingProgram (large ordinary body program)
end P
attribute [local irreducible] P.large P.ordinary P.body P.program largeCoeff
  UniformBatching.width UniformRecursiveSavingProgram.threshold

def wholeCoefficientOf (L T W : ℕ) : ℕ := L+T+4*W+10

def wholeCoeff : ℕ := wholeCoefficientOf largeCoeff UniformRecursiveSavingProgram.threshold UniformBatching.width
attribute [local irreducible] wholeCoeff

lemma whole_coefficient_bounds (L T W : ℕ) :
    L ≤ wholeCoefficientOf L T W ∧ T ≤ wholeCoefficientOf L T W ∧
    4*W+6 ≤ wholeCoefficientOf L T W ∧ 1 ≤ wholeCoefficientOf L T W := by
  unfold wholeCoefficientOf
  omega

lemma whole_coefficients : largeCoeff ≤ wholeCoeff ∧
    UniformRecursiveSavingProgram.threshold ≤ wholeCoeff ∧
    4*UniformBatching.width+6 ≤ wholeCoeff ∧ 1 ≤ wholeCoeff := by
  unfold wholeCoeff
  exact whole_coefficient_bounds largeCoeff UniformRecursiveSavingProgram.threshold UniformBatching.width

lemma ordinary_numeric_bound (A W K k : ℕ) (coeff : 4*W+6 ≤ A) (hk : k ≤ K) :
    4*(W*2^k)+2*2^k+4 ≤ A*(2^K*2^K) := by
  have p:=Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) hk
  have volume : 2^k ≤ 2^K*2^K:=p.trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  have one : 1 ≤ 2^K*2^K:=Nat.mul_pos (Nat.two_pow_pos K) (Nat.two_pow_pos K)
  have scaled:=Nat.mul_le_mul_right (2^K*2^K) coeff
  have data:=Nat.mul_le_mul_left (4*W+2) volume
  nlinarith

lemma ordinary_ambient (K k : ℕ) (I : ℂ) (v : Tape Tagged.T) (hk:k ≤ K)
    (len:v.len=UniformBatching.width*2^k) (before:Boolean v) :
    (run P.ordinary ((k,I),v)).peak ≤ wholeCoeff*(2^K*2^K) := by
  have pk:=ordinary_peak k I v before
  rw [len] at pk
  rw [P.ordinary]
  exact pk.trans (ordinary_numeric_bound wholeCoeff UniformBatching.width K k
    whole_coefficients.2.2.1 hk)

/-- Fixed ambient size bounds both the genuine depth counter and every
recursive peak. No child peak or output action is supplied. -/
theorem depth_peak (fuel K k : ℕ) (I : ℂ) (v : Tape Tagged.T) (hk:k ≤ K)
    (fuelCap : fuel ≤ K) (len:v.len=UniformBatching.width*2^k) (before:Boolean v) :
    (depthRun (P.ordinary.run ()) P.body.run fuel ((k,I),v)).peak ≤ wholeCoeff*(2^K*2^K) := by
  induction fuel generalizing k I v with
  | zero=>
    change max (run P.ordinary ((k,I),v)).peak 0 ≤ _
    exact max_le (ordinary_ambient K k I v hk len before) (Nat.zero_le _)
  | succ fuel ih=>
    let h:=depthRun (P.ordinary.run ()) P.body.run fuel
    change max (Code.run P.body h ((k,I),v)).peak (fuel+1) ≤ _
    have volume : K ≤ 2^K*2^K :=
      Nat.lt_two_pow_self.le.trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
    have fuelB : fuel+1 ≤ wholeCoeff*(2^K*2^K) :=
      (fuelCap.trans volume).trans (Nat.le_mul_of_pos_left _ whole_coefficients.2.2.2)
    refine max_le ?_ fuelB
    rw [DFTModelSavingCost.body_run]
    have one : 1 ≤ 2^K*2^K:=Nat.mul_pos (Nat.two_pow_pos K) (Nat.two_pow_pos K)
    have threshold:UniformRecursiveSavingProgram.threshold ≤ wholeCoeff*(2^K*2^K):=by
      have c:=whole_coefficients.2.1
      exact c.trans (Nat.le_mul_of_pos_right _ one)
    by_cases small:k<UniformRecursiveSavingProgram.threshold
    · rw [ite_eq_left small]
      change max (max (run P.ordinary ((k,I),v)).peak 0) UniformRecursiveSavingProgram.threshold ≤ _
      exact max_le (max_le (ordinary_ambient K k I v hk len before) (Nat.zero_le _)) threshold
    · rw [ite_eq_right small]
      change max (Code.run P.large h ((k,I),v)).peak UniformRecursiveSavingProgram.threshold ≤ _
      refine max_le ?_ threshold
      have geom:=UniformRecursiveSavingExecution.recursive_geometry k (Nat.le_of_not_gt small)
      have preserve:∀z:Node.T,Boolean z.2→Boolean (h z).val:=by
        rintro ⟨⟨j,J⟩,bank⟩ good
        exact DFTModelSavingClosedBoolean.depth_boolean fuel j J bank good
      have children:∀J (bank:Tape Tagged.T),bank.len=UniformBatching.width*2^(k/m)→Boolean bank→
          (h ((k/m,J),bank)).peak ≤ wholeCoeff*(2^K*2^K):=by
        intro J bank childLen good
        exact ih (k/m) J bank ((Nat.div_le_self _ _).trans hk)
          ((Nat.le_succ fuel).trans fuelCap) childLen good
      have pk:=large_peak h k (wholeCoeff*(2^K*2^K)) I v geom.1 len before preserve children
      apply pk.trans
      apply max_le le_rfl
      have coeff:=whole_coefficients.1
      have p:=Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) hk
      exact Nat.mul_le_mul coeff (Nat.mul_le_mul p p)

/-- Closed saving AST polynomial peak for genuine full-W banks and arbitrary
Boolean dependency tags. Prepared complex I is unrestricted. -/
theorem program_peak_bound (k : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (len:v.len=UniformBatching.width*2^k) (before:Boolean v) :
    (run P.program ((k,I),v)).peak ≤ wholeCoeff*(2^k*2^k) := by
  rw [DFTModelSavingProgram.program_run]
  change max (depthRun (P.ordinary.run ()) P.body.run k ((k,I),v)).peak k ≤ _
  refine max_le (depth_peak k k k I v le_rfl le_rfl len before) ?_
  have c:=whole_coefficients.2.2.2
  have p:k ≤ 2^k*2^k:=Nat.lt_two_pow_self.le.trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  exact p.trans (Nat.le_mul_of_pos_left _ c)

/-- A fixed quadratic polynomial; no cache, child action or peak callback is
supplied by the caller. This theorem does not assert whole-compiler work. -/
theorem polynomial_peak : ∃C:ℕ,∀k I (v:Tape Tagged.T),
    v.len=UniformBatching.width*2^k→Boolean v→
    (run P.program ((k,I),v)).peak ≤ C*(2^k+1)^2 := by
  refine ⟨wholeCoeff,?_⟩
  intro k I v len before
  apply (program_peak_bound k I v len before).trans
  apply Nat.mul_le_mul_left
  simpa only [pow_two] using
    Nat.mul_le_mul (Nat.le_succ (2^k)) (Nat.le_succ (2^k))
end
end ExactFourierCircuits.DFTModelSavingPeak

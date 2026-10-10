import DFTModelSavingFuelWork
import DFTModelSavingNativeSequence
import DFTModelSavingNativeLargePrefix

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingClosedLarge
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine DFTModelSavingBillCongruence
open UniformFixedNetwork UniformNativeScheduleSemantics UniformRecursiveTypedBody
noncomputable section
namespace P
export DFTModelSavingProgram (program large body ordinary)
end P
attribute [local irreducible] P.program P.large P.body P.ordinary
  DFTModelSavingRecords.stream DFTModelSavingBinarySuffix.program

/-- Exact closed-entry charge at a genuine large exponent. The recursive
handler is the actual predecessor depth, used once for each paired child. -/
theorem program_run (k : ℕ) (large : UniformRecursiveSavingProgram.threshold≤k)
    (I : ℂ) (v : Tape Tagged.T) :
    Related (run P.program ((k,I),v))
      ((Code.run P.large (DFTModelSavingSelfCall.evaluate (k-1)) ((k,I),v)).pay 17 k) := by
  have positive:0<k:=lt_of_lt_of_le (by decide : 0<UniformRecursiveSavingProgram.threshold) large
  obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  rw [Nat.succ_sub_one,DFTModelSavingProgram.program_run]
  change Related ((DFTModelSavingSelfCall.evaluate (j+1) ((j+1,I),v)).pay 7 (j+1)) _
  rw [DFTModelSavingSelfCall.evaluate_succ,DFTModelSavingCost.body_run,
    ite_eq_right (by omega : ¬j+1<UniformRecursiveSavingProgram.threshold)]
  constructor
  · rfl
  · change _+9+1+7=_+17
    simp only [Nat.succ_eq_add_one]

lemma recordFold_typed (q rest : ℕ) (I : ℂ) (h : Handler ChildPort)
    (is : List TypedInstruction)
    (f f0 : Fin UniformBatching.width → Fin (2^(q*m+rest)) → UniformMachine.Scalar) :
    DFTModelSavingChronology.recordFold UniformBatching.width rest h
      (is.map (Instruction.record q)) ((q*m+rest,I),DFTModelRecursiveScalarSource.paired f f0)=
      DFTModelSavingNativeSequence.typedFold q rest I h is f f0 :=
  DFTModelSavingClosedBody.recordFold_map UniformBatching.width rest h (Instruction.record q) is _

attribute [local irreducible] DFTModelSavingNativeSequence.typedFold instructions

/-- The source-facing large output is the same actual typed chronological
fold and suffix that the finite decoder executes. -/
theorem program_value (q rest : ℕ) (large : UniformRecursiveSavingProgram.threshold ≤ q*m+rest)
    (rp : rest < m) (I : ℂ)
    (f f0 : Fin UniformBatching.width → Fin (2^(q*m+rest)) → UniformMachine.Scalar) :
    (run P.program ((q*m+rest,I),DFTModelRecursiveScalarSource.paired f f0)).val=
      (run DFTModelSavingBinarySuffix.program
        (q*m,DFTModelSavingNativeSequence.typedFold q rest I
          (DFTModelSavingSelfCall.evaluate (q*m+rest-1)) instructions f f0)).val.2 := by
  have related:=program_run (q*m+rest) large I (DFTModelRecursiveScalarSource.paired f f0)
  rw [related.1]
  change (Code.run P.large (DFTModelSavingSelfCall.evaluate (q*m+rest-1)) _).val=_
  rw [DFTModelSavingControl.large_value,DFTModelSavingChronology.actual_seed_value]
  obtain ⟨quotient,modulo⟩:=DFTModelSavingNativeNode.quotient_remainder q rest rp
  rw [quotient,modulo,←records_actual,recordFold_typed]

end
end ExactFourierCircuits.DFTModelSavingClosedLarge

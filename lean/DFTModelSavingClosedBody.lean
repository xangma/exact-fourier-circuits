import DFTModelSavingSelfCall
import DFTModelSavingChronology
import UniformRecursiveCoreSchedule

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingClosedBody
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine DFTModelSavingChronology
noncomputable section
attribute [local irreducible] DFTModelSavingProgram.program DFTModelSavingProgram.ordinary
  DFTModelSavingProgram.large DFTModelSavingBinarySuffix.program
  DFTModelSavingRecords.dispatch DFTModelSavingRecords.stream DFTModelCacheRecords.seed

/-- The same closed child is invoked by each real runtime record. No handler,
ready record tape or semantic action is an input to this equation. -/
theorem program_value (k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    (run DFTModelSavingProgram.program ((k,I),v)).val=
      if k<UniformRecursiveSavingProgram.threshold then
        (run DFTModelSavingProgram.ordinary ((k,I),v)).val
      else (run DFTModelSavingBinarySuffix.program
        (k/UniformFixedNetwork.m*UniformFixedNetwork.m,
          recordFold UniformBatching.width (k%UniformFixedNetwork.m)
            (run DFTModelSavingProgram.program)
            (UniformFixedNetworkScheduleMachine.scheduleRecords (k/UniformFixedNetwork.m))
            ((k,I),v))).val.2 := by
  rw [DFTModelSavingSelfCall.recursive_value]
  split_ifs
  · rfl
  · rw [DFTModelSavingControl.large_value,actual_seed_value]

lemma recordFold_map {α : Type} (R rest : ℕ) (h : Handler ChildPort)
    (f : α→UniformFixedNetworkScheduleMachine.Record) (xs : List α) (node : Node.T) :
    recordFold R rest h (xs.map f) node=
      xs.foldl (fun current i=>recordStep R rest h (f i) current) node := by
  induction xs generalizing node with
  | nil=>rfl
  | cons a xs ih=>exact ih _

/-- The concrete stream agrees with the already proved corrected fixed-network
chronology. The finite list remains symbolic, so this theorem does not
materialize the enormous seed or replace its records by a callback. -/
theorem typed_program_value (k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    (run DFTModelSavingProgram.program ((k,I),v)).val=
      if k<UniformRecursiveSavingProgram.threshold then
        (run DFTModelSavingProgram.ordinary ((k,I),v)).val
      else (run DFTModelSavingBinarySuffix.program
        (k/UniformFixedNetwork.m*UniformFixedNetwork.m,
          UniformNativeScheduleSemantics.instructions.foldl
            (fun current i=>recordStep UniformBatching.width (k%UniformFixedNetwork.m)
              (run DFTModelSavingProgram.program)
              (UniformNativeScheduleSemantics.Instruction.record (k/UniformFixedNetwork.m) i) current)
            ((k,I),v))).val.2 := by
  rw [program_value,←UniformNativeScheduleSemantics.records_actual,recordFold_map]

end
end ExactFourierCircuits.DFTModelSavingClosedBody

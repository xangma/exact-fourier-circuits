import DFTModelSavingWorkCongruence

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingWorkCongruence
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine DFTModelSavingRecords
open DFTModelSavingBillCongruence
namespace P
export DFTModelSavingProgram (setup seedArgs suffixArgs large ordinary small body program)
end P
noncomputable section
attribute [local irreducible] DFTModelCacheRecords.seed DFTModelSavingRecords.stream
  DFTModelSavingBinarySuffix.program P.ordinary

lemma seed_tape_columns (q i : ℕ)
    (hi : i<(DFTModelCacheRecords.recordTape
      (UniformFixedNetworkScheduleMachine.scheduleRecords q)).len) :
    ((DFTModelCacheRecords.recordTape (UniformFixedNetworkScheduleMachine.scheduleRecords q)).look
      i (Tape.empty ℕ)).look 1 0=q := by
  have h:=DFTModelSavingControl.seed_columns q i
  rw [DFTModelCacheRecords.seed_value] at h
  exact h hi

lemma large_related (h h' : Handler Port) (k : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (same : HandlerRelated (k/UniformFixedNetwork.m) h h') :
    Related (P.large.run h ((k,I),v)) (P.large.run h' ((k,I),v)) := by
  unfold P.large
  apply comp_at
  · exact closed _ _ _ _
  · change Related (Code.run _ h (run P.setup ((k,I),v)).val)
      (Code.run _ h' (run P.setup ((k,I),v)).val)
    rw [DFTModelSavingProgram.setup_run]
    apply comp
    · apply fork
      · exact refl _
      · apply comp_at
        · exact closed _ _ _ _
        · change Related (Code.run _ h (run P.seedArgs _).val)
            (Code.run _ h' (run P.seedArgs _).val)
          rw [DFTModelSavingProgram.seedArgs_value]
          exact stream_related UniformBatching.width (k/UniformFixedNetwork.m)
            (k%UniformFixedNetwork.m) _ _ h h' (seed_tape_columns _) same
    · intro y
      apply comp
      · exact closed _ _ _ _
      · intro z
        apply comp
        · exact closed _ _ _ _
        · intro t
          exact refl _

/-- The exact selected body keeps work unchanged when genuine child values
and work agree at the derived smaller exponent. -/
lemma body_related (h h' : Handler Port) (k : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (same : HandlerRelated (k/UniformFixedNetwork.m) h h') :
    Related (P.body.run h ((k,I),v)) (P.body.run h' ((k,I),v)) := by
  unfold P.body
  apply ifz_closed
  · exact large_related h h' k I v same
  · exact closed _ _ _ _

end
end ExactFourierCircuits.DFTModelSavingWorkCongruence

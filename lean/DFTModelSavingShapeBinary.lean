import DFTModelSavingShapeBoolean
import DFTModelSavingBinarySuffixSemantics

set_option autoImplicit false

/-! Actual binary-stage flags are charged zero/nonzero tests. They remain
Boolean for arbitrary prepared coefficients and arbitrary input flag patterns. -/
namespace ExactFourierCircuits.DFTModelSavingShapeBinary
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualBoolean
noncomputable section

attribute [local irreducible] DFTModelBinaryPacking.program

lemma flags_boolean (u v : Tagged.T) : DFTModelBinaryAffinePair.flags u v<2 := by
  unfold DFTModelBinaryAffinePair.flags
  split <;> decide

lemma affine_pairs_boolean (M : ℕ) (c d : ℂ) (v : Tape DFTModelBinaryAffinePair.Pair.T) (j : ℕ) :
    ((run DFTModelBinaryAffine.program (M,((c,d),v))).val.look j
      DFTModelBinaryAffinePair.Pair.blank).1.1<2 ∧
    ((run DFTModelBinaryAffine.program (M,((c,d),v))).val.look j
      DFTModelBinaryAffinePair.Pair.blank).2.1<2 := by
  rw [DFTModelBinaryAffine.program_value]
  by_cases live : j<M
  · rw [Tape.look_of_lt _ _ live]
    exact ⟨flags_boolean _ _,flags_boolean _ _⟩
  · rw [Tape.look_of_le _ _ (by change M≤j;omega)]
    exact ⟨by decide,by decide⟩

lemma physical_pairs_boolean (M P : ℕ) (c d : ℂ) (v : Tape Tagged.T) (j : ℕ) :
    ((run DFTModelBinaryPhysical.program (M,(P,((c,d),v)))).val.look j
      DFTModelBinaryAffinePair.Pair.blank).1.1<2 ∧
    ((run DFTModelBinaryPhysical.program (M,(P,((c,d),v)))).val.look j
      DFTModelBinaryAffinePair.Pair.blank).2.1<2 := by
  change ((run DFTModelBinaryAffine.program
    (run DFTModelBinaryPhysical.ready (M,(P,((c,d),v)))).val).val.look j
      DFTModelBinaryAffinePair.Pair.blank).1.1<2 ∧
    ((run DFTModelBinaryAffine.program
    (run DFTModelBinaryPhysical.ready (M,(P,((c,d),v)))).val).val.look j
      DFTModelBinaryAffinePair.Pair.blank).2.1<2
  rw [DFTModelBinaryPhysical.ready_run]
  exact affine_pairs_boolean _ _ _ _ j

lemma stage_boolean (M P : ℕ) (c d : ℂ) (v : Tape Tagged.T) :
    Boolean (run DFTModelBinaryStage.program (M,(P,((c,d),v)))).val := by
  rw [DFTModelBinaryStage.program_value,DFTModelBinaryUnpacking.program_value]
  apply tab_boolean
  intro j _
  unfold DFTModelBinaryUnpacking.cellValue
  have h:=physical_pairs_boolean M P c d v (DFTModelBinaryUnpacking.indexValue P j)
  split
  · exact h.1
  · exact h.2

lemma next_boolean (I : ℂ) (P : ℕ) (v : Tape Tagged.T) :
    Boolean (DFTModelRecursiveBinary.next I P v) := stage_boolean _ _ _ _ _

lemma states_boolean (I : ℂ) (v : Tape Tagged.T) (before : Boolean v) (j : ℕ) :
    Boolean (DFTModelRecursiveBinary.states I v j).2 := by
  cases j with
  | zero=>exact before
  | succ j=>exact next_boolean _ _ _

theorem ordinary_boolean (k : ℕ) (I : ℂ) (v : Tape Tagged.T) (before : Boolean v) :
    Boolean (run DFTModelRecursiveBinary.program ((k,I),v)).val := by
  rw [DFTModelRecursiveBinary.program_value]
  exact states_boolean I v before k

lemma suffix_stages_boolean (b k : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (before : Boolean v) (j : ℕ) :
    Boolean (DFTModelSavingBinarySuffix.stages b k I v j).val.2 := by
  cases j with
  | zero=>exact before
  | succ j=>
    change Boolean (run DFTModelSavingBinarySuffix.body ((b,((k,I),v)),
      (j,(DFTModelSavingBinarySuffix.stages b k I v j).val))).val.2
    rcases h : (DFTModelSavingBinarySuffix.stages b k I v j).val with ⟨P,bank⟩
    rw [DFTModelSavingBinarySuffix.body_run]
    change Boolean (run DFTModelRecursiveBinary.body (((k,I),v),(j,(P,bank)))).val.2
    rw [DFTModelRecursiveBinary.body_value]
    exact next_boolean _ _ _

theorem suffix_boolean (b k : ℕ) (I : ℂ) (v : Tape Tagged.T) (before : Boolean v) :
    Boolean (run DFTModelSavingBinarySuffix.program (b,((k,I),v))).val.2 := by
  rw [DFTModelSavingBinarySuffix.program_run]
  change Boolean (run DFTModelSavingBinarySuffix.tapeProgram (b,((k,I),v))).val
  rw [DFTModelSavingBinarySuffix.tapeProgram,DFTModelRecursiveScalarCore.comp_run,
    DFTModelSavingBinarySuffix.loop_run]
  exact suffix_stages_boolean b k I v before (k-b)

end
end ExactFourierCircuits.DFTModelSavingShapeBinary

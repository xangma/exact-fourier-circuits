import DFTModelSavingControl
import DFTModelSavingShapeBoolean
import DFTModelSavingShapeBinary

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingClosedBoolean
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine DFTModelSavingResidualBoolean
noncomputable section
namespace P
export DFTModelSavingProgram (large ordinary body program)
end P
attribute [local irreducible] P.large P.ordinary P.body P.program
  DFTModelCacheRecords.seed DFTModelSavingRecords.stream
  DFTModelSavingBinarySuffix.program

lemma large_boolean (h : Handler ChildPort) (k : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (before : Boolean v) (children : ∀z : Node.T,Boolean z.2→Boolean (h z).val) :
    Boolean (P.large.run h ((k,I),v)).val := by
  rw [DFTModelSavingControl.large_value]
  let u:=(DFTModelSavingRecords.stream UniformBatching.width).run h
    (k%UniformFixedNetwork.m,((run DFTModelCacheRecords.seed (k/UniformFixedNetwork.m)).val,((k,I),v)))
  have output:=DFTModelSavingShapeBoolean.stream_boolean UniformBatching.width
    (k%UniformFixedNetwork.m) (run DFTModelCacheRecords.seed (k/UniformFixedNetwork.m)).val
    ((k,I),v) h before children
  change Boolean u.val.2 at output
  rcases eu:u.val with ⟨⟨j,J⟩,bank⟩
  rw [eu] at output
  exact DFTModelSavingShapeBinary.suffix_boolean _ j J bank output

lemma body_boolean (h : Handler ChildPort) (k : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (before : Boolean v) (children : ∀z : Node.T,Boolean z.2→Boolean (h z).val) :
    Boolean (P.body.run h ((k,I),v)).val := by
  rw [DFTModelSavingControl.body_value]
  split_ifs
  · rw [P.ordinary]
    exact DFTModelSavingShapeBinary.ordinary_boolean k I v before
  · exact large_boolean h k I v before children

/-- Every internal recursion depth preserves Boolean dependency flags on all
active cells. This allows arbitrary flag patterns and does not assert a
canonical tensor tag fold or prepared output role. -/
theorem depth_boolean (fuel k : ℕ) (I : ℂ) (v : Tape Tagged.T) (before : Boolean v) :
    Boolean (depthRun (P.ordinary.run ()) P.body.run fuel ((k,I),v)).val := by
  induction fuel generalizing k I v with
  | zero=>
    change Boolean (run P.ordinary ((k,I),v)).val
    rw [P.ordinary]
    exact DFTModelSavingShapeBinary.ordinary_boolean k I v before
  | succ fuel ih=>
    change Boolean (P.body.run (depthRun (P.ordinary.run ()) P.body.run fuel) ((k,I),v)).val
    apply body_boolean _ k I v before
    rintro ⟨⟨j,J⟩,bank⟩ good
    exact ih j J bank good

theorem program_boolean (k : ℕ) (I : ℂ) (v : Tape Tagged.T) (before : Boolean v) :
    Boolean (run P.program ((k,I),v)).val := by
  rw [DFTModelSavingProgram.program_run]
  exact depth_boolean k k I v before

end
end ExactFourierCircuits.DFTModelSavingClosedBoolean

import DFTModelSavingControl
import DFTModelSavingShape
import DFTModelSavingCostSuffix

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingClosedShape
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockControl DFTModelAffine
noncomputable section
namespace P
export DFTModelSavingProgram (large ordinary body program)
end P
attribute [local irreducible] P.large P.ordinary P.body P.program
  DFTModelCacheRecords.seed DFTModelSavingRecords.stream
  DFTModelSavingBinarySuffix.program

lemma suffix_length (b k : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (even : 2*(v.len/2)=v.len) :
    (run DFTModelSavingBinarySuffix.program (b,((k,I),v))).val.2.len=v.len := by
  rw [DFTModelSavingBinarySuffix.program_run,DFTModelSavingBinarySuffix.tapeProgram,
    DFTModelRecursiveScalarCore.comp_run,DFTModelSavingBinarySuffix.loop_run]
  exact DFTModelSavingCost.suffix_stages_length b k I v even (k-b)

lemma large_length (h : Handler ChildPort) (k : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (even : 2*(v.len/2)=v.len) :
    (P.large.run h ((k,I),v)).val.len=v.len := by
  rw [DFTModelSavingControl.large_value]
  let u:=(DFTModelSavingRecords.stream UniformBatching.width).run h
    (k%UniformFixedNetwork.m,((run DFTModelCacheRecords.seed (k/UniformFixedNetwork.m)).val,((k,I),v)))
  have preserved:=DFTModelSavingShape.stream_preserves UniformBatching.width
    (k%UniformFixedNetwork.m) (run DFTModelCacheRecords.seed (k/UniformFixedNetwork.m)).val ((k,I),v) h
  change u.val.1=(k,I) ∧ u.val.2.len=v.len at preserved
  rcases eu:u.val with ⟨⟨j,J⟩,bank⟩
  rw [eu] at preserved
  rw [suffix_length _ _ _ bank (by rw [preserved.2];exact even),preserved.2]

lemma body_length (h : Handler ChildPort) (k : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (even : 2*(v.len/2)=v.len) :
    (P.body.run h ((k,I),v)).val.len=v.len := by
  rw [DFTModelSavingControl.body_value]
  split_ifs
  · rw [P.ordinary]
    exact DFTModelRecursiveBinary.program_len k I v even
  · exact large_length h k I v even

/-- Even physical banks retain their length at every fuel level, for arbitrary
Scalar tags and affine coordinates. No child output or action is assumed. -/
theorem depth_length (fuel k : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (even : 2*(v.len/2)=v.len) :
    (depthRun (P.ordinary.run ()) P.body.run fuel ((k,I),v)).val.len=v.len := by
  cases fuel with
  | zero=>
    change (run P.ordinary ((k,I),v)).val.len=v.len
    rw [P.ordinary]
    exact DFTModelRecursiveBinary.program_len k I v even
  | succ fuel=>exact body_length _ k I v even

theorem program_length (k : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (even : 2*(v.len/2)=v.len) :
    (run P.program ((k,I),v)).val.len=v.len := by
  rw [DFTModelSavingProgram.program_run]
  exact depth_length k k I v even

end
end ExactFourierCircuits.DFTModelSavingClosedShape

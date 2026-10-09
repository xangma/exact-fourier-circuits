import DFTModelAffineOffsets
import DFTModelAdmissibilityControl

set_option autoImplicit false

/-! Exact affine encoding relative to the paired zero-input source run.
The typed program executes once and returns both components. -/
namespace ExactFourierCircuits.DFTModelAffine
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAdmissibilityControl
noncomputable section

def encodePaired (a zero : Scalar) : Tagged.T :=
  tagged a.dependent zero.value (a.value-zero.value)

theorem encodePaired_represents (a zero : Scalar) (same : ScalarMatch a zero) :
    Represents (encodePaired a zero) a := by
  refine ⟨rfl,?_,?_⟩
  · change a.value = zero.value + (a.value-zero.value)
    ring
  · intro h
    change a.value-zero.value = 0
    rw [same.prepared h,sub_self]

/-- One actual upstream primitive returns the complete affine encoding of
the paired successful source results. No second typed execution is used. -/
theorem paired_field_success (op : FieldOp) (a b a0 b0 result result0 : Scalar)
    (sameA : ScalarMatch a a0) (sameB : ScalarMatch b b0)
    (actual : evalField op a b = some result)
    (baseline : evalField op a0 b0 = some result0) :
    (run (field op) (encodePaired a a0,encodePaired b b0)).valid ∧
    (run (field op) (encodePaired a a0,encodePaired b b0)).val =
      encodePaired result result0 ∧
    ScalarMatch result result0 ∧
    (run (field op) (encodePaired a a0,encodePaired b b0)).work ≤ 39 ∧
    (run (field op) (encodePaired a a0,encodePaired b b0)).peak ≤ 1 := by
  have checked := field_success op a b result a0.value (a.value-a0.value)
    b0.value (b.value-b0.value)
    (encodePaired_represents a a0 sameA) (encodePaired_represents b b0 sameB) actual
  have zeroRun : evalField op ⟨a0.value,a.dependent⟩ ⟨b0.value,b.dependent⟩ =
      some result0 := by
    cases a0
    cases b0
    simpa only [sameA.flags,sameB.flags] using baseline
  have offset := field_offset_success op a.dependent b.dependent
    a0.value (a.value-a0.value) b0.value (b.value-b0.value) result0 zeroRun
  obtain ⟨r0,run0,sameResult⟩ := evalField_match sameA sameB actual
  have resultEq : r0 = result0 := Option.some.inj (run0.symm.trans baseline)
  subst r0
  have homogeneous :
      (run (field op) (encodePaired a a0,encodePaired b b0)).val.2.2 =
        result.value-result0.value := by
    dsimp only [encodePaired]
    have value := checked.2.2.1
    rw [offset] at value
    linear_combination -value
  have encoded :
      (run (field op) (encodePaired a a0,encodePaired b b0)).val =
        encodePaired result result0 := by
    apply Prod.ext checked.2.1
    exact Prod.ext offset homogeneous
  exact ⟨checked.1,encoded,sameResult,
    field_budget op a.dependent b.dependent a0.value (a.value-a0.value)
      b0.value (b.value-b0.value)⟩

end
end ExactFourierCircuits.DFTModelAffine

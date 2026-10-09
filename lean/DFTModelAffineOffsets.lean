import DFTModelAffineCorrectness

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelAffine
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine
noncomputable section

/-- Changing homogeneous inputs cannot change the prepared output offset. -/
theorem field_offset_independent (op : FieldOp) (da db : Bool) (oa ha ob hb : ℂ) :
    (run (field op) (tagged da oa ha,tagged db ob hb)).val.2.1 =
      (run (field op) (tagged da oa 0,tagged db ob 0)).val.2.1 := by
  cases op <;> cases da <;> cases db <;> simp only [field]
  all_goals first
    | rw [taggedAdd_run,taggedAdd_run]
    | rw [taggedSub_run,taggedSub_run]
    | rw [taggedMul_left_run,taggedMul_left_run]
    | rw [taggedMul_right_run,taggedMul_right_run]
    | rw [taggedMul_invalid_run,taggedMul_invalid_run]
    | rw [taggedDiv_run,taggedDiv_run]
    | rw [taggedDiv_left_invalid_run,taggedDiv_left_invalid_run]
    | rw [taggedDiv_right_invalid_run,taggedDiv_right_invalid_run]
  all_goals rfl

theorem field_zero_homogeneous (op : FieldOp) (da db : Bool) (oa ob : ℂ) :
    (run (field op) (tagged da oa 0,tagged db ob 0)).val.2.2 = 0 := by
  cases op <;> cases da <;> cases db <;> simp only [field]
  all_goals first
    | rw [taggedAdd_run]
    | rw [taggedSub_run]
    | rw [taggedMul_left_run]
    | rw [taggedMul_right_run]
    | rw [taggedMul_invalid_run]
    | rw [taggedDiv_run]
    | rw [taggedDiv_left_invalid_run]
    | rw [taggedDiv_right_invalid_run]
  all_goals simp [tagged]

/-- The offset follows the source's zero-input scalar computation with the
same conservative taint flags, including tainted zero-valued operands. -/
theorem field_offset_success (op : FieldOp) (da db : Bool) (oa ha ob hb : ℂ)
    (result : Scalar)
    (zeroRun : evalField op ⟨oa,da⟩ ⟨ob,db⟩ = some result) :
    (run (field op) (tagged da oa ha,tagged db ob hb)).val.2.1 = result.value := by
  have ra : Represents (tagged da oa 0) ⟨oa,da⟩ := by
    simp [Represents,tagged]
  have rb : Represents (tagged db ob 0) ⟨ob,db⟩ := by
    simp [Represents,tagged]
  have represented := (field_success op ⟨oa,da⟩ ⟨ob,db⟩ result oa 0 ob 0 ra rb zeroRun).2
  have value := represented.2.1
  rw [field_zero_homogeneous,add_zero] at value
  exact (field_offset_independent op da db oa ha ob hb).trans value.symm

end
end ExactFourierCircuits.DFTModelAffine

import DFTModelAffine

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelAffine
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine
noncomputable section

/-- Every successful source primitive is represented by the genuine typed
program, including mixed prepared/data additions with nonzero offsets. -/
theorem field_success (op : FieldOp) (a b result : Scalar) (oa ha ob hb : ℂ)
    (ra : Represents (tagged a.dependent oa ha) a)
    (rb : Represents (tagged b.dependent ob hb) b)
    (success : evalField op a b = some result) :
    (run (field op) (tagged a.dependent oa ha,tagged b.dependent ob hb)).valid ∧
    Represents (run (field op)
      (tagged a.dependent oa ha,tagged b.dependent ob hb)).val result := by
  rcases a with ⟨va,da⟩
  rcases b with ⟨vb,db⟩
  rcases ra with ⟨_,rva,rha⟩
  rcases rb with ⟨_,rvb,rhb⟩
  by_cases den : vb = 0
  all_goals cases op <;> cases da <;> cases db
  all_goals simp only [evalField,Bool.or_false,
    Bool.or_true,Bool.and_false,Bool.and_true,
    Bool.false_eq_true,ite_false,ite_true] at success
  all_goals first
    | rw [ite_eq_left den] at success
    | rw [ite_eq_right den] at success
    | skip
  all_goals try contradiction
  all_goals have result_eq := Option.some.inj success
  all_goals subst result
  all_goals simp only [field]
  all_goals first
    | rw [taggedAdd_run]
    | rw [taggedSub_run]
    | rw [taggedMul_left_run]
    | rw [taggedMul_right_run]
    | rw [taggedDiv_run]
  all_goals dsimp only [tagged] at rva rvb rha rhb
  all_goals simp at rha rhb
  all_goals simp_all [Represents,tagged,flag]
  all_goals first
    | (solve | ring)
    | (solve | linear_combination den)
    | (solve | linear_combination -den)
    | (solve | linear_combination oa * den)
    | (solve | linear_combination -oa * den)

end
end ExactFourierCircuits.DFTModelAffine

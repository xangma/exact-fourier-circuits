import DFTModelSavingCostFixed

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
noncomputable section
attribute [local irreducible] unitAllowance

lemma fixed_unit_coefficients (m R : ℕ) :
    1000≤recordUnit m R ∧ 127+179*R≤recordUnit m R ∧ 74+131*R≤recordUnit m R := by
  unfold recordUnit
  constructor
  · omega
  constructor <;> nlinarith

lemma charge_at_least_local (A weight V recursive : ℕ) (positive : 1≤weight) :
    A*V≤A*weight*V+recursive := by
  have cap:=Nat.mul_le_mul_right V (Nat.mul_le_mul_left A positive)
  simp only [Nat.mul_one] at cap
  exact cap.trans (Nat.le_add_right _ _)

end
end ExactFourierCircuits.DFTModelSavingCost

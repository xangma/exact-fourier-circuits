import DFTModelSavingCostFactor

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
noncomputable section
attribute [local irreducible] unitAllowance nativeWorkFactor

lemma fixed_padding_control (m R : ℕ) : unitAllowance+52≤recordUnit m R := by
  unfold recordUnit
  omega

/-- The actual unit printer and all 52 charged role-control instructions fit
inside the same fixed work factor used by recursive children. -/
lemma factor_padding_control : unitAllowance+52≤nativeWorkFactor :=
  (fixed_padding_control UniformFixedNetwork.m UniformBatching.width).trans factor_local

end
end ExactFourierCircuits.DFTModelSavingCost

import DFTModelSavingCostFixed

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
noncomputable section
attribute [local irreducible] unitAllowance recordUnit seedAllowance

lemma fixed_local_caps (m R : ℕ) :
    20*R+200≤recordUnit m R ∧ 32*(R+1)+71≤recordUnit m R ∧
    603*m+1347+104*R+unitAllowance≤recordUnit m R ∧ 1000≤recordUnit m R := by
  unfold recordUnit
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · omega

lemma fixed_unit_print (m R : ℕ) : unitAllowance+51≤recordUnit m R := by
  unfold recordUnit
  omega

/-- A genuine fixed finite constant. Its opaque subtype avoids evaluating the
astronomical static seed syntax during kernel conversion. -/
private opaque nativeWorkReserve : {K : ℕ // recordUnit UniformFixedNetwork.m UniformBatching.width+seedAllowance+2000≤K} :=
  ⟨recordUnit UniformFixedNetwork.m UniformBatching.width+seedAllowance+2000,le_rfl⟩
def nativeWorkFactor : ℕ := nativeWorkReserve.val
lemma nativeWorkFactor_lower :
    recordUnit UniformFixedNetwork.m UniformBatching.width+seedAllowance+2000≤nativeWorkFactor :=
  nativeWorkReserve.property

lemma reserve_parts (A seed K : ℕ) (bound : A+seed+2000≤K) : A≤K ∧ seed+87≤K := by omega
lemma factor_local : recordUnit UniformFixedNetwork.m UniformBatching.width≤nativeWorkFactor :=
  (reserve_parts _ _ _ nativeWorkFactor_lower).1
lemma factor_preparation : seedAllowance+87≤nativeWorkFactor :=
  (reserve_parts _ _ _ nativeWorkFactor_lower).2
lemma factor_marker : 1000≤nativeWorkFactor :=
  (fixed_local_caps UniformFixedNetwork.m UniformBatching.width).2.2.2.trans factor_local
lemma factor_suffix : 32≤nativeWorkFactor := (by omega : 32≤1000).trans factor_marker
lemma factor_scalar_exchange : 20*UniformBatching.width+200≤nativeWorkFactor :=
  (fixed_local_caps UniformFixedNetwork.m UniformBatching.width).1.trans factor_local
lemma factor_translation : 32*(UniformBatching.width+1)+71≤nativeWorkFactor :=
  (fixed_local_caps UniformFixedNetwork.m UniformBatching.width).2.1.trans factor_local
lemma factor_padding_unit : unitAllowance+51≤nativeWorkFactor :=
  (fixed_unit_print UniformFixedNetwork.m UniformBatching.width).trans factor_local
lemma factor_direction (rest : ℕ) (hr : rest < UniformFixedNetwork.m) :
    363*UniformFixedNetwork.m+240*rest+1347+104*UniformBatching.width≤nativeWorkFactor := by
  have cap:363*UniformFixedNetwork.m+240*rest+1347+104*UniformBatching.width≤
      603*UniformFixedNetwork.m+1347+104*UniformBatching.width+unitAllowance := by omega
  exact cap.trans ((fixed_local_caps UniformFixedNetwork.m UniformBatching.width).2.2.1.trans factor_local)

end
end ExactFourierCircuits.DFTModelSavingCost

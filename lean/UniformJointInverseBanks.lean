import UniformJointAllocation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformJointInverseBanks
open UniformJointAllocation
lemma roles_volume (c : Constants) (n : ℕ) (hn : 0 < n) :
 c.roles*UniformInitialPreparation.len n ≤ slab c n := by
 have h:=actual_arithmetic c n hn
 dsimp only at h
 rw [Nat.mul_assoc 2 c.roles] at h
 omega
/-- Real reverse movement banks fit below the common recursive fresh frontier. -/
lemma separation (c : Constants) (n : ℕ) (hn : 0 < n) :
 let U:=slab c n
 let R:=c.roles*UniformInitialPreparation.len n
 6*U+R ≤ 7*U ∧ 7*U+R ≤ 8*U ∧ 8*U+R ≤ 12*U ∧
 2*U+R ≤ 7*U ∧ 8*U+R ≤ envelope c n ∧ 2*U+R ≤ envelope c n := by
 intro U R
 have r:R ≤ U:=roles_volume c n hn
 change _ ∧ _ ∧ _ ∧ _ ∧ _ ≤ 40*U+fixed c ∧ _ ≤ 40*U+fixed c
 omega
end ExactFourierCircuits.UniformJointInverseBanks

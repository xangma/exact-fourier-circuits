import UniformRecursiveBodyGeometry
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveReserve
open UniformFixedNetworkScheduleMachine UniformRecursiveNodePreparation
noncomputable section
namespace P
export UniformRecursiveSavingProgram (seedLength unitLength threshold)
end P

def payload:ℕ:=P.seedLength+P.unitLength+6
private opaque choice:{R:ℕ // P.seedLength+P.unitLength+11≤R ∧P.threshold≤R ∧ExplicitSeedBudget.m+1≤R ∧
 literalCap (serialize baseSchedule)≤R ∧34≤R}:=
 ⟨P.seedLength+P.unitLength+11+P.threshold+(ExplicitSeedBudget.m+1)+literalCap (serialize baseSchedule)+34,by omega⟩
def reserve:ℕ:=choice.val
lemma payload_fit:P.seedLength+P.unitLength+11≤reserve:=choice.property.1
lemma threshold_fit:P.threshold≤reserve:=choice.property.2.1
lemma width_fit:ExplicitSeedBudget.m+1≤reserve:=choice.property.2.2.1
lemma literals_fit:literalCap (serialize baseSchedule)≤reserve:=choice.property.2.2.2.1
lemma stack_fit:34≤reserve:=choice.property.2.2.2.2

lemma stack_room {F k B:ℕ}(room:F+reserve*(k+1)*2^k≤B):F+34*(k+1)≤B:=by
 have v:1≤2^k:=Nat.two_pow_pos k
 have a:=Nat.mul_le_mul_right (k+1) stack_fit
 have b:=Nat.mul_le_mul_left (reserve*(k+1)) v
 simp only [Nat.mul_one] at b
 omega
end
end ExactFourierCircuits.UniformRecursiveReserve

import UniformRecursiveActualRuntime
import UniformRecursiveBatchGroupMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveTypedNodeArithmetic
open UniformFixedNetwork
noncomputable section

lemma quotient_at (q rest : ℕ) (hr : rest < m) : UniformBatching.quotient (q*m+rest)=q := by
 change (q*m+rest)/m=q
 rw [Nat.add_comm,Nat.mul_comm q m,Nat.add_mul_div_left _ _ (by decide : 0 < m),Nat.div_eq_of_lt hr]
 omega

lemma groups_at (q rest : ℕ) (hr : rest < m) :
 UniformRecursiveBatchGroupMachine.groupCount q (m-1) rest=UniformBatching.batchCount (q*m+rest) := by
 unfold UniformRecursiveBatchGroupMachine.groupCount UniformBatching.batchCount
 rw [quotient_at q rest hr]
 apply congrArg (fun t=>2^t)
 have one : m-1+1=m := Nat.sub_add_cancel (by decide)
 have product:=congrArg (fun t=>q*t) one
 simp only [Nat.mul_add,Nat.mul_one] at product
 change q*(m-1)+rest-ExplicitSeedBudget.roleBits=q*m+rest-q-ExplicitSeedBudget.roleBits
 omega

/-- Transport a named local allowance through the exact q/remainder and group
 identities. Every actual same-q child retains its169 charged return overhead. -/
theorem node_charge (q rest workTicks : ℕ) (hr : rest < m)
 (hk : UniformRecursiveRuntimeBridge.actualThreshold ≤ q*m+rest)
 (work : workTicks ≤ UniformRecursiveActualLocalAllowance.localUnit*UniformNetworkCost.volume (q*m+rest)) :
 workTicks+UniformFixedNetwork.S*UniformRecursiveBatchGroupMachine.groupCount q (m-1) rest*
 (UniformRecursiveRuntimeBridge.costWithUnit UniformRecursiveActualRuntime.stepUnit q+169) ≤ 
 UniformRecursiveRuntimeBridge.costWithUnit UniformRecursiveActualRuntime.stepUnit (q*m+rest) := by
 have cap:=UniformRecursiveActualRuntime.actual_node_call_charge hk workTicks work
 rw [quotient_at q rest hr] at cap
 have eq:=congrArg (fun g=>workTicks+UniformFixedNetwork.S*g*
  (UniformRecursiveRuntimeBridge.costWithUnit UniformRecursiveActualRuntime.stepUnit q+169)) (groups_at q rest hr)
 exact eq.le.trans cap

end
end ExactFourierCircuits.UniformRecursiveTypedNodeArithmetic

import UniformRecursiveNamedPreparationReserve
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveActualLocalAllowance
open UniformFixedNetworkScheduleMachine
noncomputable section

private opaque localReserve : {A : ℕ //
 UniformRecursiveNamedPreparationReserve.preparationTicks+
 2000*(UniformFixedNetwork.m+1)*(UniformFixedNetwork.S+
 (serialize baseSchedule).length+UniformBatching.width+1) ≤ A} :=
 ⟨UniformRecursiveNamedPreparationReserve.preparationTicks+
 2000*(UniformFixedNetwork.m+1)*(UniformFixedNetwork.S+
 (serialize baseSchedule).length+UniformBatching.width+1),le_rfl⟩

def localUnit : ℕ := localReserve.val
lemma localUnit_lower :
 UniformRecursiveNamedPreparationReserve.preparationTicks+
 2000*(UniformFixedNetwork.m+1)*(UniformFixedNetwork.S+
 (serialize baseSchedule).length+UniformBatching.width+1) ≤ localUnit :=
 localReserve.property

lemma width_positive : 1 ≤ UniformBatching.width := by
 rw [UniformBatching.width_eq_pow]
 exact Nat.two_pow_pos _

/-- Actual named printers, exact actual schedule inventory and full terminal suffix.
Only the suffix's address remainder constraints are required. -/
theorem actual_local_allowance (q k b : ℕ) (hb:b ≤ k)
 (hr:k-b < UniformFixedNetwork.m) :
 UniformRecursiveSavingProgram.seedPrinterLength+12+
 UniformRecursiveSavingProgram.unitPrinterLength+15+50+
 UniformRecursiveLocalAllowance.tapeAllowance UniformFixedNetwork.m k (scheduleRecords q)+
 (4*b+UniformBatching.width*UniformBinarySpectatorCMachine.arrayCost k b+21) ≤
 localUnit*(UniformBatching.width*2^k) := by
 have h:=UniformRecursiveLocalAllowance.node_bound
  UniformRecursiveNamedPreparationReserve.preparationTicks UniformFixedNetwork.m
  UniformFixedNetwork.S (serialize baseSchedule).length UniformBatching.width (2^k)
  (UniformRecursiveSavingProgram.seedPrinterLength+12+
   UniformRecursiveSavingProgram.unitPrinterLength+15+50)
  (UniformRecursiveLocalAllowance.tapeAllowance UniformFixedNetwork.m k (scheduleRecords q))
  (4*b+UniformBatching.width*UniformBinarySpectatorCMachine.arrayCost k b+21)
  (Nat.two_pow_pos _) width_positive
  UniformRecursiveNamedPreparationReserve.actual_producer_bound
  (UniformRecursiveLocalAllowance.schedule_allowance q k)
  (UniformRecursiveLocalAllowance.suffix_bound k b UniformBatching.width UniformFixedNetwork.m
   hb width_positive hr)
 exact h.trans (Nat.mul_le_mul_right (UniformBatching.width*2^k) localUnit_lower)

end
end ExactFourierCircuits.UniformRecursiveActualLocalAllowance

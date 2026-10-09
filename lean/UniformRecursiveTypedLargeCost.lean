import UniformRecursiveTypedCostAllowance
import UniformRecursiveTypedNodeArithmetic
import UniformRecursivePrintedBody

set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveTypedLargeCost
open UniformFixedNetwork UniformFixedNetworkScheduleMachine UniformRecursiveCoreSchedule UniformRecursiveTypedBody
noncomputable section

lemma controls (seed unit ready body records suffix tape calls : ℕ)
 (readyBound : ready ≤ 15) (bodyEq : body=records+(suffix+20)) (recordBound : records ≤ tape+calls) :
 20+(seed+12+unit+ready)+body ≤ 
 (seed+12+unit+15+50+tape+(suffix+21))+calls := by omega

lemma actual_body_value (q rest : ℕ) (cost : ℕ→ℕ) :
 UniformRecursivePrintedBody.bodyTicks q rest cost=
 ((coreInstructions.map (ticks q rest cost)).sum+UniformRecursiveTypedCostAllowance.paddingTicks q rest cost)+
 (4*(q*m)+W*UniformBinarySpectatorCMachine.arrayCost (q*m+rest) (q*m)+20) := rfl

/-- Exact actual large-child prologue, real printers, full typed body and
spectator terminal fit the existing opaque recurrence unit. The only inputs
are quotient/remainder arithmetic and the actual large-branch threshold. -/
theorem large_node_bound (q rest : ℕ) (hq : 1 ≤ q) (hr : rest < m)
 (hk : UniformRecursiveRuntimeBridge.actualThreshold ≤ q*m+rest) :
 20+(UniformRecursiveSavingProgram.seedPrinterLength+12+
 UniformRecursiveSavingProgram.unitPrinterLength+UniformRecursiveSavingProgram.size .nodeReady)+
 UniformRecursivePrintedBody.bodyTicks q rest
  (UniformRecursiveRuntimeBridge.costWithUnit UniformRecursiveActualRuntime.stepUnit) ≤ 
 UniformRecursiveRuntimeBridge.costWithUnit UniformRecursiveActualRuntime.stepUnit (q*m+rest) := by
 have recordBound:=UniformRecursiveTypedCostAllowance.core_padding_bound q rest
  (UniformRecursiveRuntimeBridge.costWithUnit UniformRecursiveActualRuntime.stepUnit) hq hr
 have controlsBound:=controls UniformRecursiveSavingProgram.seedPrinterLength
  UniformRecursiveSavingProgram.unitPrinterLength (UniformRecursiveSavingProgram.size .nodeReady)
  (UniformRecursivePrintedBody.bodyTicks q rest (UniformRecursiveRuntimeBridge.costWithUnit UniformRecursiveActualRuntime.stepUnit))
  ((coreInstructions.map (ticks q rest (UniformRecursiveRuntimeBridge.costWithUnit UniformRecursiveActualRuntime.stepUnit))).sum+
   UniformRecursiveTypedCostAllowance.paddingTicks q rest (UniformRecursiveRuntimeBridge.costWithUnit UniformRecursiveActualRuntime.stepUnit))
  (4*(q*m)+W*UniformBinarySpectatorCMachine.arrayCost (q*m+rest) (q*m))
  (UniformRecursiveLocalAllowance.tapeAllowance m (q*m+rest) (scheduleRecords q))
  (UniformFixedNetwork.S*UniformRecursiveBatchGroupMachine.groupCount q (m-1) rest*
   (UniformRecursiveRuntimeBridge.costWithUnit UniformRecursiveActualRuntime.stepUnit q+169))
  (by change 15 ≤ 15;exact le_rfl) (actual_body_value q rest _) recordBound
 have localBound:=UniformRecursiveActualLocalAllowance.actual_local_allowance q (q*m+rest) (q*m)
  (by omega) (by simpa only [Nat.add_sub_cancel_left] using hr)
 have charged:=UniformRecursiveTypedNodeArithmetic.node_charge q rest
  (UniformRecursiveSavingProgram.seedPrinterLength+12+UniformRecursiveSavingProgram.unitPrinterLength+15+50+
   UniformRecursiveLocalAllowance.tapeAllowance m (q*m+rest) (scheduleRecords q)+
   (4*(q*m)+UniformBatching.width*UniformBinarySpectatorCMachine.arrayCost (q*m+rest) (q*m)+21))
  hr hk localBound
 exact controlsBound.trans charged

end
end ExactFourierCircuits.UniformRecursiveTypedLargeCost

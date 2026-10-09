import UniformRecursiveActualLocalAllowance

/-!
Paper correspondence: An explicit power saving for the exact discrete Fourier
transform, OpenAI math revision adc7f1241b42e322a6451854ab7e4b4c146bf78a,
§2.6, Theorem 2.6 recurrence and geometric-series argument, PDF pp. 11–12 (net:tensor-bound).
The fixed operational threshold is larger than the paper’s K. The proof enlarges the finite base constant while retaining exactly S, lambda and theta. Opaque reserve values are defined constants with proved bounds, not new axioms.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveActualRuntime
open UniformNetworkCost
noncomputable section
namespace R
export UniformRecursiveRuntimeBridge (actualThreshold baseTicks baseUnit costWithUnit)
end R

/- Paper: Concrete constant bounding the fixed work A in Theorem 2.6, pp. 11–12. Its value has an explicit defining witness; opacity prevents unnecessary expansion of gigantic fixed tables. -/
private opaque stepReserve : {A : ℕ //
 UniformRecursiveActualLocalAllowance.localUnit+169*ExplicitSeedBudget.residuals ≤ A} :=
 ⟨UniformRecursiveActualLocalAllowance.localUnit+169*ExplicitSeedBudget.residuals,le_rfl⟩
def stepUnit : ℕ := stepReserve.val
lemma stepUnit_lower :
 UniformRecursiveActualLocalAllowance.localUnit+169*ExplicitSeedBudget.residuals ≤ stepUnit :=
 stepReserve.property

def recurrenceUnit : ℕ := stepUnit+R.baseUnit
noncomputable def criticalConstant : ℝ :=
 ((recurrenceUnit:ℝ)/(UniformExponent.lambda-1)+R.baseUnit)*UniformExponent.lambda

lemma threshold_lower : UniformBatching.threshold ≤ R.actualThreshold := by
 rw [UniformBatching.threshold,UniformBatching.blockSize_eq,UniformBatching.roleBits_eq,
  UniformRecursiveRuntimeBridge.actualThreshold,ExplicitSeedBudget.bits_value]
 norm_num

lemma actual_recurrence (k : ℕ) :
 R.costWithUnit stepUnit k ≤ recurrenceUnit*volume k+
 ExplicitSeedBudget.residuals*UniformBatching.batchCount k*
 R.costWithUnit stepUnit (UniformBatching.quotient k) :=
 UniformRecursiveRuntimeBridge.costWithUnit_recurrence stepUnit R.baseUnit
  (fun _ h=>UniformRecursiveRuntimeBridge.baseTicks_bound h)

lemma actual_base {k : ℕ} (hk:k < UniformBatching.threshold) :
 R.costWithUnit stepUnit k ≤ R.baseUnit*volume k := by
 rw [UniformRecursiveRuntimeBridge.costWithUnit_base stepUnit (hk.trans_le threshold_lower)]
 exact UniformRecursiveRuntimeBridge.baseTicks_bound (hk.trans_le threshold_lower)

/-- Unconditional asymptotic bound for the actual-printer-compatible arithmetic cost.
A whole Program execution proof is still required. -/
/- Paper: Theorem 2.6, p. 12: the normalized recurrence t(k) <= A + lambda*t(floor(k/m)) is unrolled geometrically at the critical exponent log_m(lambda). -/
theorem actual_critical_bound (k : ℕ) :
 (R.costWithUnit stepUnit k:ℝ) ≤
 criticalConstant*(k+1:ℝ)^UniformExponent.theta*(volume k:ℝ) :=
 UniformRecursiveRuntimeBridge.nat_critical_bound (R.costWithUnit stepUnit)
 recurrenceUnit R.baseUnit (fun k _=>actual_recurrence k) (fun _ h=>actual_base h) k

theorem actual_isBigO :
 (fun k : ℕ=>(R.costWithUnit stepUnit k:ℝ)) =O[Filter.atTop]
 (fun k : ℕ=>(k+1:ℝ)^UniformExponent.theta*(volume k:ℝ)) := by
 apply Asymptotics.IsBigO.of_bound criticalConstant
 filter_upwards [] with k
 rw [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (by positivity)]
 simpa only [mul_assoc] using actual_critical_bound k

/-- Charges each actual recursive call's169steps, using the checked local allowance. -/
theorem actual_node_call_charge {k : ℕ} (hk:R.actualThreshold ≤ k) (workTicks : ℕ)
 (work:workTicks ≤ UniformRecursiveActualLocalAllowance.localUnit*volume k) :
 workTicks+ExplicitSeedBudget.residuals*UniformBatching.batchCount k*
 (R.costWithUnit stepUnit (UniformBatching.quotient k)+169) ≤ R.costWithUnit stepUnit k := by
 exact (UniformRecursiveRuntimeBridge.group_charge ExplicitSeedBudget.residuals
  (UniformBatching.batchCount k) (volume k)
  (R.costWithUnit stepUnit (UniformBatching.quotient k))
  UniformRecursiveActualLocalAllowance.localUnit stepUnit workTicks
  (UniformRecursiveRuntimeBridge.batch_le_volume (threshold_lower.trans hk)) stepUnit_lower work).trans_eq
  (UniformRecursiveRuntimeBridge.costWithUnit_step stepUnit hk).symm

/-- Exact named printers, actual tape and terminal controls fit the chosen recurrence. -/
/- Paper: Theorem 2.6, pp. 11–12: actual table printing, local tape, spectator arithmetic and call/return overhead all enter the recurrence; this lemma is exact implementation accounting. -/
theorem actual_static_node_charge (q k b : ℕ) (hk:R.actualThreshold ≤ k)
 (hb:b ≤ k) (hr:k-b < UniformFixedNetwork.m) :
 (UniformRecursiveSavingProgram.seedPrinterLength+12+
 UniformRecursiveSavingProgram.unitPrinterLength+15+50+
 UniformRecursiveLocalAllowance.tapeAllowance UniformFixedNetwork.m k
  (UniformFixedNetworkScheduleMachine.scheduleRecords q)+
 (4*b+UniformBatching.width*UniformBinarySpectatorCMachine.arrayCost k b+21))+
 ExplicitSeedBudget.residuals*UniformBatching.batchCount k*
 (R.costWithUnit stepUnit (UniformBatching.quotient k)+169) ≤ R.costWithUnit stepUnit k :=
 actual_node_call_charge hk _ (UniformRecursiveActualLocalAllowance.actual_local_allowance q k b hb hr)

end
end ExactFourierCircuits.UniformRecursiveActualRuntime

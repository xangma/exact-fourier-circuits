import UniformNetworkCost
import UniformBinarySpectatorCMachine
import UniformResidualGeneralPreparation
import UniformNativeYRecordMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveRuntimeBridge
open UniformNetworkCost
noncomputable section
namespace Y
export UniformNativePreparedYTranslationMachine (runtime tableCost)
end Y

/-- Full scalar record, including actual common-loop read and dispatch. -/
lemma scalar_bound (k c : ℕ) (hc : c < 5) :
 10*2^k+4*k+c+102 ≤ 120*2^k := by
 have h:k ≤ 2^k:=Nat.lt_two_pow_self.le
 have hp:1 ≤ 2^k:=Nat.two_pow_pos k
 omega

lemma exchange_bound (k pairs : ℕ) :
 (10*2^k+21)*pairs+4*k+99 ≤ (31*pairs+103)*2^k := by
 have h:k ≤ 2^k:=Nat.lt_two_pow_self.le
 have hp:1 ≤ 2^k:=Nat.two_pow_pos k
 nlinarith

/-- The actual q-by-q XOR table does not add a q factor to array work. -/
lemma preparedY_bound (q m r : ℕ) (hm : 3 ≤ m) (hr : r < m) :
 Y.runtime q m r (q*m+r) ≤ (34*m+90)*2^(q*m+r) := by
 have fit:3*q ≤ q*m+r:=by nlinarith
 have table:=UniformXorWordBounds.table_cost_array_bound q (q*m+r) fit
 have length:q*m ≤ 2^(q*m+r):=(Nat.le_add_right (q*m) r).trans Nat.lt_two_pow_self.le
 have hp:1 ≤ 2^(q*m+r):=Nat.two_pow_pos _
 unfold Y.runtime Y.tableCost UniformResidualNativeTranslationMachine.volume
 nlinarith

lemma translation_bound (q m r rows : ℕ) (hm : 3 ≤ m) (hr : r < m) :
 UniformNativeYRecordMachine.runtime q m r (q*m+r) rows+47 ≤ 
 ((34*m+101)*rows+103)*2^(q*m+r) := by
 have prep:=preparedY_bound q m r hm hr
 have length:q*m+r ≤ 2^(q*m+r):=Nat.lt_two_pow_self.le
 have hp:1 ≤ 2^(q*m+r):=Nat.two_pow_pos _
 have row:=Nat.mul_le_mul_left rows (show Y.runtime q m r (q*m+r)+11 ≤ (34*m+101)*2^(q*m+r) by nlinarith)
 unfold UniformNativeYRecordMachine.runtime
 nlinarith

/-- Native gather includes all q*(m-1)+r spectators in one traversal. -/
lemma gather_bound (q m r : ℕ) (hq : 1 ≤ q) (hm : 3 ≤ m) (hr : r < m)
 (header : ℕ) (hh : header ≤ 38) :
 header+18+UniformResidualGeneralPreparation.runtimeBound q m r+
 11*2^(q*m+r)+11 ≤ (58*m+347)*2^(q*m+r) := by
 have run:=UniformResidualGeneralPreparation.runtime_linear q m r hq hm hr
 have hp:1 ≤ 2^(q*m+r):=Nat.two_pow_pos _
 nlinarith

/-- Physical inverse translation after a copied child, with all spectators. -/
lemma inverse_bound (q m r : ℕ) (hr : r < m) :
 (17*(m+r)+25)*2^(q*m+r)+13 ≤ (34*m+38)*2^(q*m+r) := by
 have hp:1 ≤ 2^(q*m+r):=Nat.two_pow_pos _
 nlinarith

lemma base_array_bound (k : ℕ) :
 UniformBinaryBatchCMachine.arrayCost k ≤ (36*k+16)*2^k := by
 have hp:1 ≤ 2^k:=Nat.two_pow_pos _
 have hs:2^(k-1) ≤ 2^k:=Nat.pow_le_pow_right (by omega) (by omega)
 unfold UniformBinaryBatchCMachine.arrayCost
 have hm:=Nat.mul_le_mul_left k (show 25*2^(k-1)+11 ≤ 36*2^k by omega)
 nlinarith

/-- A reserve for physical base batch and bounded entry/return controls.
The execution theorem must still show its exact ticks fit this reserve. -/
def baseTicks (k : ℕ) : ℕ := UniformBatching.width*UniformBinaryBatchCMachine.arrayCost k+4*k+500

def actualThreshold : ℕ := ExplicitSeedBudget.bits

def preparationTicks : ℕ :=
 3*(UniformFixedNetworkScheduleMachine.serialize UniformFixedNetworkScheduleMachine.baseSchedule).length+
 3*UniformFixedNetworkScheduleMachine.baseSchedule.length+3*(8+ExplicitSeedBudget.m^2)+1000

/-- Fixed literal-table size is retained symbolically. The existing tableCharge
reserve has no established operational relation to this producer. -/
def localUnit : ℕ := preparationTicks+
 2000*(ExplicitSeedBudget.m+1)*(ExplicitSeedBudget.residuals+
  (UniformFixedNetworkScheduleMachine.serialize UniformFixedNetworkScheduleMachine.baseSchedule).length+
  UniformBatching.width+1)

private opaque stepReserve : {A : ℕ // localUnit+169*ExplicitSeedBudget.residuals ≤ A} :=
 ⟨localUnit+169*ExplicitSeedBudget.residuals,le_rfl⟩
private opaque baseReserve : {B : ℕ // 36*actualThreshold+520 ≤ B} :=
 ⟨36*actualThreshold+520,le_rfl⟩
def stepUnit : ℕ := stepReserve.val
def baseUnit : ℕ := baseReserve.val
lemma stepUnit_lower : localUnit+169*ExplicitSeedBudget.residuals ≤ stepUnit := stepReserve.property
lemma baseUnit_lower : 36*actualThreshold+520 ≤ baseUnit := baseReserve.property

def recurrenceUnit : ℕ := stepUnit+baseUnit

def costWithUnit (A k : ℕ) : ℕ :=
 if _hk : k < actualThreshold then baseTicks k
 else A*volume k+ExplicitSeedBudget.residuals*UniformBatching.batchCount k*
  costWithUnit A (UniformBatching.quotient k)
termination_by k
decreasing_by
 apply UniformBatching.quotient_lt
 have h:UniformBatching.threshold ≤ actualThreshold:=by
  rw [UniformBatching.threshold,UniformBatching.blockSize_eq,UniformBatching.roleBits_eq,
   actualThreshold,ExplicitSeedBudget.bits_value]
  norm_num
 exact h.trans (Nat.le_of_not_gt _hk)

lemma baseTicks_bound {k : ℕ} (hk : k < actualThreshold) : baseTicks k ≤ baseUnit*volume k := by
 have width:1 ≤ UniformBatching.width:=by rw [UniformBatching.width_eq_pow];exact Nat.two_pow_pos _
 have hp:1 ≤ 2^k:=Nat.two_pow_pos _
 have h:k ≤ 2^k:=Nat.lt_two_pow_self.le
 have work:2^k ≤ volume k:=by unfold volume;exact Nat.le_mul_of_pos_left _ width
 have hm:=Nat.mul_le_mul_left UniformBatching.width (base_array_bound k)
 have first:UniformBatching.width*UniformBinaryBatchCMachine.arrayCost k ≤ (36*k+16)*volume k:=by
  unfold volume
  nlinarith
 have cap:36*k+520 ≤ baseUnit:=
  (show 36*k+520 ≤ 36*actualThreshold+520 by omega).trans baseUnit_lower
 have up:=Nat.mul_le_mul_right (volume k) cap
 unfold baseTicks
 nlinarith

lemma costWithUnit_base (A : ℕ) {k : ℕ} (hk : k < actualThreshold) : costWithUnit A k=baseTicks k := by
 rw [costWithUnit,dite_eq_left hk]
lemma costWithUnit_step (A : ℕ) {k : ℕ} (hk : actualThreshold ≤ k) :
 costWithUnit A k=A*volume k+ExplicitSeedBudget.residuals*UniformBatching.batchCount k*
  costWithUnit A (UniformBatching.quotient k) := by
 rw [costWithUnit,dite_eq_right (Nat.not_lt.mpr hk)]

lemma base_weaken (A B v rest t : ℕ) (h : t ≤ B*v) : t ≤ (A+B)*v+rest :=
 h.trans ((Nat.mul_le_mul_right v (Nat.le_add_left B A)).trans (Nat.le_add_right _ rest))
lemma step_weaken (A B v rest : ℕ) : A*v+rest ≤ (A+B)*v+rest :=
 Nat.add_le_add_right (Nat.mul_le_mul_right v (Nat.le_add_right A B)) rest

lemma costWithUnit_recurrence (A B : ℕ) (base : ∀k,k < actualThreshold→baseTicks k ≤ B*volume k)
 {k : ℕ} : costWithUnit A k ≤ (A+B)*volume k+
 ExplicitSeedBudget.residuals*UniformBatching.batchCount k*costWithUnit A (UniformBatching.quotient k) := by
 by_cases h:k < actualThreshold
 · rw [costWithUnit_base A h]
   exact base_weaken A B (volume k) _ _ (base k h)
 · rw [costWithUnit_step A (Nat.le_of_not_gt h)]
   exact step_weaken A B (volume k) _

abbrev chargedCost : ℕ→ℕ := costWithUnit stepUnit

lemma chargedCost_base {k : ℕ} (hk : k < actualThreshold) : costWithUnit stepUnit k=baseTicks k :=
 costWithUnit_base stepUnit hk
lemma chargedCost_step {k : ℕ} (hk : actualThreshold ≤ k) :
 costWithUnit stepUnit k=stepUnit*volume k+ExplicitSeedBudget.residuals*UniformBatching.batchCount k*
  costWithUnit stepUnit (UniformBatching.quotient k) := costWithUnit_step stepUnit hk

/-- Safe enlargement handles the genuine larger operational base threshold.
The recursive coefficient is still exactly S, including opcode5. -/
lemma chargedCost_recurrence {k : ℕ} (_hk : UniformBatching.threshold ≤ k) :
 costWithUnit stepUnit k ≤ recurrenceUnit*volume k+ExplicitSeedBudget.residuals*UniformBatching.batchCount k*
  costWithUnit stepUnit (UniformBatching.quotient k) :=
 costWithUnit_recurrence stepUnit baseUnit (fun _ h=>baseTicks_bound h)

lemma chargedCost_base_bound {k : ℕ} (hk : k < UniformBatching.threshold) :
 costWithUnit stepUnit k ≤ baseUnit*volume k := by
 have threshold:UniformBatching.threshold ≤ actualThreshold:=by
  rw [UniformBatching.threshold,UniformBatching.blockSize_eq,UniformBatching.roleBits_eq,
   actualThreshold,ExplicitSeedBudget.bits_value]
  norm_num
 have h:=hk.trans_le threshold
 rw [chargedCost_base h]
 exact baseTicks_bound h

noncomputable def chargedConstant : ℝ :=
 ((recurrenceUnit:ℝ)/(UniformExponent.lambda-1)+baseUnit)*UniformExponent.lambda

lemma batch_le_volume {k : ℕ} (hk : UniformBatching.threshold ≤ k) :
 UniformBatching.batchCount k ≤ volume k := by
 have one : 1 ≤ volume (UniformBatching.quotient k) := UniformNetworkCost.volume_pos _
 have small : UniformBatching.batchCount k ≤ 2^k :=
  (Nat.le_mul_of_pos_right _ one).trans_eq (UniformBatching.batch_partition hk)
 have wide : 2^k ≤ volume k := by
  unfold volume
  exact Nat.le_mul_of_pos_left _ (by rw [UniformBatching.width_eq_pow];exact Nat.two_pow_pos _)
 exact small.trans wide

lemma group_charge (S batches V child L A workTicks : ℕ)
 (batch : batches ≤ V) (reserve : L+169*S ≤ A) (work : workTicks ≤ L*V) :
 workTicks+S*batches*(child+169) ≤ A*V+S*batches*child := by
 have h:=Nat.mul_le_mul_right V reserve
 have b:=Nat.mul_le_mul_left (169*S) batch
 nlinarith

/-- Charges the actual group loop's 169 call/return/control steps per child.
The workTicks execution must still establish its localUnit array allowance. -/
lemma node_call_charge {k : ℕ} (hk : actualThreshold ≤ k) (workTicks : ℕ)
 (work : workTicks ≤ localUnit*volume k) :
 workTicks+ExplicitSeedBudget.residuals*UniformBatching.batchCount k*
  (costWithUnit stepUnit (UniformBatching.quotient k)+169) ≤ costWithUnit stepUnit k := by
 have threshold:UniformBatching.threshold ≤ actualThreshold := by
  rw [UniformBatching.threshold,UniformBatching.blockSize_eq,UniformBatching.roleBits_eq,
   actualThreshold,ExplicitSeedBudget.bits_value]
  norm_num
 exact (group_charge ExplicitSeedBudget.residuals (UniformBatching.batchCount k)
  (volume k) (costWithUnit stepUnit (UniformBatching.quotient k)) localUnit stepUnit workTicks
  (batch_le_volume (threshold.trans hk)) stepUnit_lower work).trans_eq (costWithUnit_step stepUnit hk).symm

lemma nat_critical_bound (T : ℕ→ℕ) (A B : ℕ)
 (step : ∀k,UniformBatching.threshold ≤ k→T k ≤ A*volume k+
  ExplicitSeedBudget.residuals*UniformBatching.batchCount k*T (UniformBatching.quotient k))
 (base : ∀k,k < UniformBatching.threshold→T k ≤ B*volume k) (k : ℕ) :
 (T k:ℝ) ≤ ((A:ℝ)/(UniformExponent.lambda-1)+B)*UniformExponent.lambda*
  (k+1:ℝ)^UniformExponent.theta*(volume k:ℝ) := by
 exact UniformBatching.total_cost_bound_from_recurrence
  (fun j=>(T j:ℝ)) A B (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  (fun j hj=>by exact_mod_cast step j hj)
  (fun j hj=>by exact_mod_cast base j hj) k

/-- Arithmetic critical-exponent bound only. This is not a whole Program
execution theorem and does not establish UniformDFTStatement. -/
theorem chargedCost_critical_bound (k : ℕ) :
 (costWithUnit stepUnit k:ℝ) ≤ chargedConstant*(k+1:ℝ)^UniformExponent.theta*(volume k:ℝ) :=
 nat_critical_bound (costWithUnit stepUnit) recurrenceUnit baseUnit
  (fun _ h=>chargedCost_recurrence h) (fun _ h=>chargedCost_base_bound h) k

theorem chargedCost_isBigO :
 (fun k : ℕ=>(costWithUnit stepUnit k:ℝ)) =O[Filter.atTop]
  (fun k : ℕ=>(k+1:ℝ)^UniformExponent.theta*(volume k:ℝ)) := by
 apply Asymptotics.IsBigO.of_bound chargedConstant
 filter_upwards [] with k
 rw [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (by positivity)]
 simpa only [mul_assoc] using chargedCost_critical_bound k

end

end ExactFourierCircuits.UniformRecursiveRuntimeBridge

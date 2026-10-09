import UniformRecursiveActualRuntime
import UniformRecursiveResidualDirectionLoop

set_option autoImplicit false

namespace ExactFourierCircuits.UniformRecursiveV2CostAllowance
noncomputable section
open UniformFixedNetworkScheduleMachine

/-- Exact nonrecursive terms in the corrected actual direction-loop cost. -/
def directionLocal (q m r header : ℕ) : ℕ :=
 header+18+UniformResidualGeneralPreparation.runtimeBound q m r+11*2^(q*m+r)+16+
 1+1+13+7*m+max ((17*(m+r)+35)*2^(q*m+r)+39) (10*2^(q*m+r)+12)+3

lemma directionLocal_bound (q m r header : ℕ) (hq : 1 ≤ q) (hm : 3 ≤ m)
 (hr : r < m) (hh : header ≤ 38) :
 directionLocal q m r header ≤ (99*m+444)*2^(q*m+r) := by
 have gather := UniformRecursiveRuntimeBridge.gather_bound q m r hq hm hr header hh
 have hp : 1 ≤ 2^(q*m+r) := Nat.two_pow_pos _
 have inverse : (17*(m+r)+35)*2^(q*m+r)+39 ≤ (34*m+74)*2^(q*m+r) := by nlinarith
 have scatter : 10*2^(q*m+r)+12 ≤ (34*m+74)*2^(q*m+r) := by nlinarith
 have maximum := max_le inverse scatter
 unfold directionLocal
 nlinarith

/-- This bounds the actual named directionCost, preserving its exact smaller
same-Program recursive term and the169 charged group overhead. -/
theorem actual_direction_bound (q w r header : ℕ) (cost : ℕ → ℕ)
 (hq : 1 ≤ q) (hm : 3 ≤ w+1) (hr : r < w+1) (hh : header ≤ 38) :
 UniformRecursiveResidualDirectionLoop.directionCost q w r header cost ≤
 (99*(w+1)+444)*2^(q*(w+1)+r)+
 UniformRecursiveBatchGroupMachine.groupCount q w r*(cost q+169) := by
 have h := directionLocal_bound q (w+1) r header hq hm hr hh
 unfold UniformRecursiveResidualDirectionLoop.directionCost directionLocal at *
 omega

/-- Full actual residual record, with the child term retained exactly. -/
lemma residual_record_bound (q w rest header d data : ℕ) (cost : ℕ → ℕ)
 (hq : 1 ≤ q) (hm : 3 ≤ w+1) (hr : rest < w+1) (hh : header ≤ 38) :
 53+d*UniformRecursiveResidualDirectionLoop.directionCost q w rest header cost ≤
 1000*((w+1)+1)*(d+data+1)*2^(q*(w+1)+rest)+
 d*UniformRecursiveBatchGroupMachine.groupCount q w rest*(cost q+169) := by
 have direction := actual_direction_bound q w rest header cost hq hm hr hh
 have record := UniformResidualOrientationAllowance.residual_record_bound
  (w+1) (q*(w+1)+rest) d data ((99*(w+1)+444)*2^(q*(w+1)+rest)) le_rfl
 nlinarith

/-- Padding uses all m directions of the same q-child for each padded role. -/
lemma padding_record_bound (q w rest header roles data : ℕ) (cost : ℕ → ℕ)
 (hq : 1 ≤ q) (hm : 3 ≤ w+1) (hr : rest < w+1) (hh : header ≤ 38) :
 73+roles*(64+(w+1)*UniformRecursiveResidualDirectionLoop.directionCost q w rest header cost) ≤
 1000*((w+1)+1)*(roles*(w+1)+data+1)*2^(q*(w+1)+rest)+
 (roles*(w+1))*UniformRecursiveBatchGroupMachine.groupCount q w rest*(cost q+169) := by
 have direction := actual_direction_bound q w rest header cost hq hm hr hh
 have record := UniformResidualOrientationAllowance.padding_record_bound
  (w+1) (q*(w+1)+rest) roles data ((99*(w+1)+444)*2^(q*(w+1)+rest)) (by omega) le_rfl
 have scaled := Nat.mul_le_mul_left (roles*(w+1)) direction
 nlinarith

/-- The appended pointer restoration's four actual Y instructions fit the
unchanged1000 reserve of every record. -/
lemma translation_record_bound (q m rest d data rows : ℕ) (hm : 3 ≤ m)
 (hr : rest < m) (rows_le : rows ≤ data) :
 UniformNativeYRecordMachine.runtime q m rest (q*m+rest) rows+51 ≤
 1000*(m+1)*(d+data+1)*2^(q*m+rest) := by
 have h := UniformRecursiveRuntimeBridge.translation_bound q m rest rows hm hr
 have hp : 1 ≤ 2^(q*m+rest) := Nat.two_pow_pos _
 have more := Nat.mul_le_mul_right (2^(q*m+rest)) (Nat.mul_le_mul_left (34*m+101) rows_le)
 have cap := UniformRecursiveLocalAllowance.affine_reserve m data d (2^(q*m+rest))
  (34*m+101) 107 hp (by omega) (by omega)
 nlinarith

/-- Full marker/read/dispatch controls, rather than only their final dispatch. -/
lemma marker_record_bound (m k d data header dispatch : ℕ)
 (hh : header ≤ 38) (hd : dispatch ≤ 94) :
 6+2*header+dispatch ≤ 1000*(m+1)*(d+data+1)*2^k := by
 have cap := UniformRecursiveLocalAllowance.affine_reserve m 0 (d+data) (2^k) 0 176
  (Nat.two_pow_pos _) (by omega) (by omega)
 have hp : 1 ≤ 2^k := Nat.two_pow_pos _
 simp only [Nat.zero_mul,Nat.zero_add] at cap
 nlinarith

lemma sum_charge_formula (m k groups child : ℕ) (rs : List Record) :
 (rs.map (fun r => UniformRecursiveLocalAllowance.recordAllowance m k r+
   UniformRecursiveRuntimeInventory.recursiveDirections r*groups*child)).sum =
 UniformRecursiveLocalAllowance.tapeAllowance m k rs+
 UniformRecursiveRuntimeInventory.directions rs*groups*child := by
 induction rs with
 | nil => simp [UniformRecursiveLocalAllowance.tapeAllowance,UniformRecursiveRuntimeInventory.directions]
 | cons r rs ih =>
   simp only [List.map_cons,List.sum_cons,ih,UniformRecursiveLocalAllowance.tapeAllowance,
    UniformRecursiveRuntimeInventory.directions] at *
   ring

/-- The finite sum of all typed records retains exact residual multiplicity.
Operational handlers supply their individual proved costs to this adapter. -/
theorem sum_charges (m k groups child : ℕ) (rs : List Record) (ticks : Record → ℕ)
 (bounds : ∀ r ∈ rs, ticks r ≤ UniformRecursiveLocalAllowance.recordAllowance m k r+
   UniformRecursiveRuntimeInventory.recursiveDirections r*groups*child) :
 (rs.map ticks).sum ≤ UniformRecursiveLocalAllowance.tapeAllowance m k rs+
 UniformRecursiveRuntimeInventory.directions rs*groups*child := by
 rw [← sum_charge_formula]
 induction rs with
 | nil => exact le_rfl
 | cons r rs ih =>
   simp only [List.map_cons,List.sum_cons]
   exact Nat.add_le_add (bounds r (by simp)) (ih (by intro t ht;exact bounds t (by simp [ht])))

/-- Actual static schedule inventory, without reducing its enormous literal payload. -/
theorem schedule_sum_charges (q k groups child : ℕ) (ticks : Record → ℕ)
 (bounds : ∀ r ∈ scheduleRecords q, ticks r ≤ UniformRecursiveLocalAllowance.recordAllowance UniformFixedNetwork.m k r+
   UniformRecursiveRuntimeInventory.recursiveDirections r*groups*child) :
 ((scheduleRecords q).map ticks).sum ≤
 UniformRecursiveLocalAllowance.tapeAllowance UniformFixedNetwork.m k (scheduleRecords q)+
 UniformFixedNetwork.S*groups*child := by
 have h := sum_charges UniformFixedNetwork.m k groups child (scheduleRecords q) ticks bounds
 rw [UniformRecursiveRuntimeInventory.schedule_directions] at h
 exact h

end
end ExactFourierCircuits.UniformRecursiveV2CostAllowance

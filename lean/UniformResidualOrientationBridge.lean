import UniformResidualOrientationArithmetic
import UniformResidualOrientationAllowance
import UniformResidualOrientationMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualOrientationBridge
open scoped BigOperators
open BinaryFrames
noncomputable section

lemma range_weight {w : ℕ} (v : Vec (Fin w)) :
 (∑ j ∈ Finset.range w,UniformRepeatedMaskMachine.bits v j)=
 UniformResidualOrientationArithmetic.scannerWeight v := by
 rw [← Fin.sum_univ_eq_sum_range]
 apply Finset.sum_congr rfl
 intro j _
 simp [UniformRepeatedMaskMachine.bits]

lemma residue_eq {w : ℕ} (v : Vec (Fin w)) :
 UniformResidualOrientationMachine.residue v w=
 UniformResidualOrientationArithmetic.scannerWeight v%4 := by
 unfold UniformResidualOrientationMachine.residue
 rw [range_weight]

lemma effective_code (code weight : ℕ) (hc:code<2) :
 UniformResidualOrientationMachine.effective code weight=
 (code+(if weight=3 then 1 else 0))%2 := by
 unfold UniformResidualOrientationMachine.effective
 by_cases h:weight=3
 · simp only [h,ite_true]
 · simp only [h,ite_false,Nat.add_zero,Nat.mod_eq_of_lt hc]

theorem effective_orientation {w : ℕ} (v : Vec (Fin w)) (hv:dot v v=1)
 (decreasing : Bool) :
 UniformResidualOrientationMachine.effective
 (UniformResidualOrientationArithmetic.boolCode decreasing)
 (UniformResidualOrientationMachine.residue v w)=
 UniformResidualOrientationArithmetic.boolCode
 (UniformResidualFibers.inverseOrientation v decreasing) := by
 rw [residue_eq,effective_code _ _ (by cases decreasing <;> decide)]
 exact UniformResidualOrientationArithmetic.orientation_code v hv decreasing

lemma actual_direction_bound (q m rest header w : ℕ) (v : Vec (Fin w))
 (hq:1 ≤ q) (hm:3 ≤ m) (hr:rest < m) (hh:header ≤ 38) (hw:w ≤ m) :
 UniformRecursiveLocalAllowance.directionTicks q m rest header+
 UniformResidualOrientationMachine.ticks v+1 ≤ (99*m+444)*2^(q*m+rest) := by
 have h:=UniformResidualOrientationAllowance.direction_bound q m rest header w hq hm hr hh hw
 have ticks:=UniformResidualOrientationMachine.ticks_bound v
 unfold UniformResidualOrientationAllowance.directionTicks at h
 omega

end
end ExactFourierCircuits.UniformResidualOrientationBridge

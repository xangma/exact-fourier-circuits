import UniformActualCalendarLogBounds
import UniformActualSelectedKernelCost

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarAsymptotics
open UniformActualCalendarLogBounds UniformActualKernelCost UniformNetworkCost
open UniformJointAllocation UniformJointConditionalKernelContext
open UniformFourierClockBounds Filter Asymptotics
open scoped BigOperators
noncomputable section

lemma exponent_shift (a : ℕ) : ((a+2:ℕ):ℝ)^UniformExponent.theta ≤
 (2:ℝ)^UniformExponent.theta*((a+1:ℕ):ℝ)^UniformExponent.theta:=by
 have compare:(a:ℝ)+2 ≤ 2*((a:ℝ)+1):=by have positive:=Nat.cast_nonneg (α:=ℝ) a;linarith
 have bound:=Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (a:ℝ)+2) compare UniformExponent.theta_pos.le
 rw [Real.mul_rpow (by norm_num) (by positivity)] at bound
 simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using bound

noncomputable def kernelEnvelope (W n : ℕ) : ℝ:=
 horizon n*clockConstant W*((UniformWorkingLength.axisCount n+2:ℕ):ℝ)^UniformExponent.theta*
 UniformWorkingLength.workingLength n
noncomputable def wholeConstant (W : ℕ) : ℝ:=horizonUnit*clockConstant W*(2:ℝ)^UniformExponent.theta
lemma kernelEnvelope_nonneg (W n : ℕ) : 0 ≤ kernelEnvelope W n:=by
 unfold kernelEnvelope;have positive:=clockConstant_nonneg W;positivity

/-- The real maximum full Fourier horizon times the actual same-program
kernel bound has exactly the established workingCost theta/log-four shape. -/
theorem kernelEnvelope_bound (W : ℕ) {n : ℕ} (hn : 0<n) :
 kernelEnvelope W n ≤ wholeConstant W*UniformAsymptotics.workingCost UniformExponent.theta n:=by
 have clocks:=horizon_bound hn
 have shift:=exponent_shift (UniformWorkingLength.axisCount n)
 have constant:=clockConstant_nonneg W
 have length:0 ≤ (UniformWorkingLength.workingLength n:ℝ):=Nat.cast_nonneg _
 have factor:0 ≤ ((UniformWorkingLength.axisCount n+2:ℕ):ℝ)^UniformExponent.theta:=Real.rpow_nonneg (Nat.cast_nonneg _) _
 have log:0 ≤ logFactor n^4:=pow_nonneg (le_trans zero_le_one (logFactor_one_le n)) _
 unfold kernelEnvelope
 calc
  _ = (horizon n:ℝ)*(clockConstant W*((UniformWorkingLength.axisCount n+2:ℕ):ℝ)^UniformExponent.theta*
   UniformWorkingLength.workingLength n):=by ring
  _ ≤ (horizonUnit*logFactor n^4)*(clockConstant W*((UniformWorkingLength.axisCount n+2:ℕ):ℝ)^UniformExponent.theta*
   UniformWorkingLength.workingLength n):=mul_le_mul_of_nonneg_right clocks (by positivity)
  _ = (horizonUnit*logFactor n^4*clockConstant W)*((UniformWorkingLength.axisCount n+2:ℕ):ℝ)^UniformExponent.theta*
   UniformWorkingLength.workingLength n:=by ring
  _ ≤ (horizonUnit*logFactor n^4*clockConstant W)*((2:ℝ)^UniformExponent.theta*((UniformWorkingLength.axisCount n+1:ℕ):ℝ)^UniformExponent.theta)*
   UniformWorkingLength.workingLength n:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left shift (by positivity)) length
  _ = _:=by unfold wholeConstant UniformAsymptotics.workingCost logFactor;ring

/-- Direct finite sum of the actual initialized kernel budgets at every clock
of the true full Fourier horizon. Source geometry remains factual. -/
theorem actual_clocks_bound (c : Constants) {n : ℕ} (hn : 0<n) (roles : 0<c.roles)
 (physical : Fin (horizon n)→List UniformSectorPackingMachine.PhysicalAxis)
 (shape : ∀t,PhysicalGeometry c n (physical t)) :
 ((∑t,UniformActualKernelCost.kernelTicks (actualReserveContext c n hn roles (physical t) (shape t))):ℝ) ≤
 wholeConstant c.roles*UniformAsymptotics.workingCost UniformExponent.theta n:=by
 have bound:=UniformActualSelectedKernelCost.all_clocks c hn roles (horizon n) physical shape
 have arranged: ((∑t,UniformActualKernelCost.kernelTicks (actualReserveContext c n hn roles (physical t) (shape t))):ℝ) ≤
  kernelEnvelope c.roles n:=bound.trans_eq (by unfold kernelEnvelope;ring)
 exact arranged.trans (kernelEnvelope_bound c.roles hn)

theorem kernelEnvelope_isBigO_working (W : ℕ) :
 (kernelEnvelope W)=O[atTop] UniformAsymptotics.workingCost UniformExponent.theta:=by
 apply IsBigO.of_bound (wholeConstant W)
 filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
 rw [Real.norm_of_nonneg (kernelEnvelope_nonneg W n),Real.norm_of_nonneg (UniformNetworkCost.workingCost_nonneg n)]
 exact kernelEnvelope_bound W (by omega)

theorem kernelEnvelope_isBigO_paper (W : ℕ) :
 (kernelEnvelope W)=O[atTop] UniformMachine.asymptoticCost UniformExponent.theta:=
 (kernelEnvelope_isBigO_working W).trans UniformAsymptotics.workingCost_isBigO_paper

end
end ExactFourierCircuits.UniformActualCalendarAsymptotics

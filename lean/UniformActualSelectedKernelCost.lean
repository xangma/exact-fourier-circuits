import UniformActualKernelCost
import UniformJointConditionalKernelContext

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualSelectedKernelCost
open UniformJointAllocation UniformJointConditionalKernelContext
open scoped BigOperators
noncomputable section

/-- Actual allocated context geometry converts the real initialized kernel
bound to selected working length and the one-axis theta factor. -/
theorem selected_kernel (c : Constants) {n : ℕ} (hn : 0<n) (roles : 0<c.roles)
 (physical : List UniformSectorPackingMachine.PhysicalAxis) (shape : PhysicalGeometry c n physical) :
 (UniformActualKernelCost.kernelTicks (actualReserveContext c n hn roles physical shape):ℝ) ≤
 UniformActualKernelCost.clockConstant c.roles*((UniformWorkingLength.axisCount n+2:ℕ):ℝ)^UniformExponent.theta*
 UniformWorkingLength.workingLength n:=by
 have bound:=UniformActualKernelCost.kernel_ticks_bound (actualReserveContext c n hn roles physical shape)
 have volume:(actualReserveContext c n hn roles physical shape).packing.volume=UniformWorkingLength.workingLength n:=rfl
 have length:(actualReserveContext c n hn roles physical shape).physical.length=UniformWorkingLength.axisCount n+1:=shape.length
 rw [volume,length] at bound
 norm_num only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at bound ⊢
 have offset (a : ℝ) : a+1+1=a+2:=by ring
 simpa only [offset] using bound

/-- Every real synchronized clock pays its actual sector kernel once. This
finite sum is independent of how many axis caches are prepared at that clock;
the caller supplies the genuine full Fourier clock count. -/
theorem all_clocks (c : Constants) {n : ℕ} (hn : 0<n) (roles : 0<c.roles) (T : ℕ)
 (physical : Fin T→List UniformSectorPackingMachine.PhysicalAxis)
 (shape : ∀t,PhysicalGeometry c n (physical t)) :
 ((∑t,UniformActualKernelCost.kernelTicks (actualReserveContext c n hn roles (physical t) (shape t))):ℝ) ≤
 T*(UniformActualKernelCost.clockConstant c.roles*((UniformWorkingLength.axisCount n+2:ℕ):ℝ)^UniformExponent.theta*
 UniformWorkingLength.workingLength n):=by
 have bound:=Finset.sum_le_sum (fun t (_:t∈Finset.univ)=>selected_kernel c hn roles (physical t) (shape t))
 simpa only [Nat.cast_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using bound

end
end ExactFourierCircuits.UniformActualSelectedKernelCost

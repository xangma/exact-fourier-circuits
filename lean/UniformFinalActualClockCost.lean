import UniformFinalStatementBridge
import UniformGlobalKernelDiagonalRetention
import UniformRecursiveChildInduction
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalActualClockCost
open UniformKernelDiagonalBanks UniformFinalClockOverhead UniformFinalClockCost
open UniformJointAllocation UniformJointConditionalKernelContext
noncomputable section

/-- Both operational consumers use exactly the certified same-program child
cost; this is definitional equality, not a substituted recursion estimate. -/
lemma child_cost_eq:UniformRecursiveChildInduction.cost=UniformActualSectorCost.actualCost:=rfl

lemma actual_tick_bound{W F R:ℕ}(g:Kernel (W:=W) (F:=F) (R:=R))(d:Diagonal W)(links:Links g d)
 (good:∀a∈d.entries,2 ≤ a.radix):
 UniformGlobalKernelDiagonalRetention.budget g d UniformRecursiveChildInduction.cost ≤
 UniformActualKernelCost.kernelTicks g+(130*W+100)*g.packing.volume:=by
 have extra:=diagonal_extra_linear d good
 have volume:g.packing.volume=d.tensor.volume:=links.volume.trans d.volume
 rw[←volume] at extra
 rw[child_cost_eq]
 unfold UniformGlobalKernelDiagonalRetention.budget UniformActualKernelCost.kernelTicks
 rw[←volume]
 omega

/-- The actual retained kernel+147 budget at every clock is bounded by the
proved envelope. Axis allowances are the measured389 counts; all kernel and
child terms here are their actual operational definitions. -/
theorem actual_loop_bound(c:Constants){n:ℕ}(hn:0<n)(roles:0<c.roles)
 (physical:Fin (UniformFourierClockBounds.horizon n)→List UniformSectorPackingMachine.PhysicalAxis)
 (shape:∀t,PhysicalGeometry c n (physical t))
 (diagonal:Fin (UniformFourierClockBounds.horizon n)→Diagonal c.roles)
 (links:∀t,Links (actualReserveContext c n hn roles (physical t) (shape t)) (diagonal t))
 (good:∀t,∀a∈(diagonal t).entries,2 ≤ a.radix)
 (prep selected:Fin (UniformFourierClockBounds.horizon n)→Fin (UniformAllAxisSeedPreparation.axisCount n)→ℕ)
 (axis:∀t j,prep t j+66*UniformAllAxisSeedPreparation.radix n j+233+
  selected t j*(9*UniformAllAxisSeedPreparation.radix n j+48) ≤
  axisScanBudget (UniformAllAxisSeedPreparation.radix n j)):
 (loopBudget n prep selected (fun t=>UniformGlobalKernelDiagonalRetention.budget
  (actualReserveContext c n hn roles (physical t) (shape t)) (diagonal t)
  UniformRecursiveChildInduction.cost):ℝ) ≤ clockEnvelope c.roles n:=by
 apply UniformFinalClockCost.actual_loop_bound c hn roles physical shape prep selected _ axis
 intro t
 exact actual_tick_bound _ _ (links t) (good t)

end
end ExactFourierCircuits.UniformFinalActualClockCost

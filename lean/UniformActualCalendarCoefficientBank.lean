import UniformActualCalendarShiftedPair
import UniformLocalRequestGeometry

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarCoefficientBank
noncomputable section
open OAI.ExactFourier UniformJointAllocation UniformAllAxisSeedPreparation
open UniformLocalRectangleDescriptors UniformCanonicalCacheSlotGeometry
open UniformCanonicalSelectedPhase

/-- The actual retained lane3 inverse-H coefficients and their reciprocal
coefficients are the normal rectangle renderer's shared rank bank. -/
theorem values (n:ℕ)(axisIndex:Fin (axisCount n))(q:Row) :
 (fun i:Fin (UniformToeplitzCrossDAG.bankSize (UniformWorkspacePlanner.exponent q.a q.e)) =>
  UniformRankCrossReplayPreparationMachine.bankValues
   (UniformSeedHeightPreparation.parameters n axisIndex
    (UniformLocalRectanglePhaseBanks.actual q (UniformJointCacheWorkspace.original n q)))
   (UniformSeedRankCrossPreparation.hValue n axisIndex)
   (UniformSeedRankCrossPreparation.gValue n axisIndex) i.val)=
 rowBank q (NewtonFourier.invH (zeta (radix n axisIndex))):=by
 funext i
 unfold UniformRankCrossReplayPreparationMachine.bankValues
 have hi : i.val < UniformToeplitzCrossDAG.bankSize
   (UniformSeedHeightPreparation.parameters n axisIndex
    (UniformLocalRectanglePhaseBanks.actual q (UniformJointCacheWorkspace.original n q))).base.K := i.isLt
 rw [dite_eq_left hi]
 rfl

theorem context_bank (constants:Constants)(n:ℕ)(axisIndex:Fin (axisCount n))
 (q:Row)(k time:ℕ):
 UniformLocalRectangleCacheBindings.coefficientBank axisIndex q
  (UniformJointCacheWorkspace.original n q) (context constants n axisIndex q k time)=
 rowBank q (NewtonFourier.invH (zeta (radix n axisIndex))):=
 values n axisIndex q

end
end ExactFourierCircuits.UniformActualCalendarCoefficientBank

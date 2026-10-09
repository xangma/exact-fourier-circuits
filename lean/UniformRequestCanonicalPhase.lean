import UniformRequestRectanglePackage

set_option autoImplicit false
namespace ExactFourierCircuits.UniformRequestCanonicalPhase
noncomputable section
open OAI.ExactFourier UniformJointAllocation UniformAllAxisSeedPreparation UniformLocalRequestPlan
open UniformLocalRequestGeometry UniformCalendarNativePieces UniformLocalFourierLayers
open UniformActualCalendarRectangleProduced UniformActualCalendarRectanglePhaseResult
open UniformRequestRectanglePackage

variable {constants:Constants}{n:ℕ}{axisIndex:Fin (axisCount n)}{qs:List Request}{R T:ℕ}
 (g:Geometry constants n axisIndex qs R T){s:UniformMachine.State}
 (all:∀i (hi:i<qs.length),Complete constants n axisIndex qs R T g i hi s)
 (i:ℕ)(hi:i<qs.length)(j:ℕ)(hj:j<slotCount n qs[i].row)

def actualPackage:
 Package (envelope constants n) n axisIndex qs[i].row j s
  (controller constants n axisIndex qs i) where
 ha:=aBound constants n axisIndex qs i hi
 he:=eBound constants n axisIndex qs i hi
 positive:=(g.slots i hi).positive
 data:=UniformActualCalendarRectangleRegistry.data g all i hi j hj

/-- The exact registry factory has the canonical local rectangle phase,
derived from its genuine cache witness and seed bank. -/
def phase_result
 {hf:PowerSeries.constantCoeff (NewtonFourier.invH (zeta (radix n axisIndex)))≠0}
 {L:List (Layer qs[i].row.width)}
 (actual:Core (NewtonFourier.invH (zeta (radix n axisIndex))) hf (.rectangle qs[i].row) L)
 (extent:qs[i].row.offset+qs[i].row.width≤radix n axisIndex)(elapsed:ℕ)(below:elapsed<28):
 Result ((UniformActualCalendarRectangleRegistry.data g all i hi j hj).event _ _ _ _ _ _ _ _ elapsed)
  (UniformChunkPortMachine.intervalEmbedding (radix n axisIndex) qs[i].row.offset qs[i].row.width extent)
  L (28*j+elapsed):=by
 let p:=actualPackage g all i hi j hj
 let p':=cast (controller_eq constants n axisIndex qs i hi) p
 have result:=UniformActualCalendarRectanglePhaseResult.phase_result constants n axisIndex qs[i].row
  (slotPrefix n qs i) qs[i].time j p'.ha p'.he p'.positive p'.data actual extent elapsed below
 have same:p'.event elapsed=p.event elapsed:=cast_event _ p elapsed
 change Result (p.event elapsed) _ _ _
 rw[←same]
 exact result

end
end ExactFourierCircuits.UniformRequestCanonicalPhase

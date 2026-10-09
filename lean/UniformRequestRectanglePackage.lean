import UniformActualCalendarRectanglePhaseResult
import UniformActualCalendarRectangleRegistry

set_option autoImplicit false
namespace ExactFourierCircuits.UniformRequestRectanglePackage
noncomputable section
open UniformMachine UniformJointAllocation UniformAllAxisSeedPreparation
open UniformLocalRectangleDescriptors UniformLocalCacheSlotConductorMachine
open UniformActualCalendarRectangleProduced

/-- Context transport retains the complete real cache witness, including its
dependent coefficient-bank and width proofs. -/
structure Package (B n:ℕ)(axisIndex:Fin (axisCount n))(q:Row)(j:ℕ)(s:State)
 (c:Header.Parameters) where
 ha:q.a≤UniformCrossHeightPreparationMachine.widthOf c.height
 he:q.e≤UniformCrossHeightPreparationMachine.widthOf c.height
 positive:2≤c.ambient
 data:Data (B:=B) c q ha he
  (UniformLocalRectangleCacheBindings.coefficientBank axisIndex q
   (UniformJointCacheWorkspace.original n q) c) positive j s

def Package.event {B n:ℕ}{axisIndex:Fin (axisCount n)}{q:Row}{j:ℕ}{s:State}{c:Header.Parameters}
 (p:Package B n axisIndex q j s c)(elapsed:ℕ):UniformGlobalCalendarDispatch.Event:=
 p.data.event _ _ _ _ _ _ _ _ elapsed

def cast {B n:ℕ}{axisIndex:Fin (axisCount n)}{q:Row}{j:ℕ}{s:State}{c d:Header.Parameters}
 (eq:c=d)(p:Package B n axisIndex q j s c):Package B n axisIndex q j s d:=eq▸p

lemma cast_event {B n:ℕ}{axisIndex:Fin (axisCount n)}{q:Row}{j:ℕ}{s:State}{c d:Header.Parameters}
 (eq:c=d)(p:Package B n axisIndex q j s c)(elapsed:ℕ):
 (cast eq p).event elapsed=p.event elapsed:=by
 cases eq
 rfl

lemma controller_eq (constants:Constants)(n:ℕ)(axisIndex:Fin (axisCount n))
 (qs:List UniformLocalRequestPlan.Request)(i:ℕ)(hi:i<qs.length):
 UniformLocalRequestPlan.controller constants n axisIndex qs i=
  UniformCanonicalCacheSlotGeometry.context constants n axisIndex qs[i].row
   (UniformLocalRequestPlan.slotPrefix n qs i) qs[i].time:=by
 rw[UniformLocalRequestPlan.controller,UniformLocalRequestPlan.requestAt_eq qs i hi]

end
end ExactFourierCircuits.UniformRequestRectanglePackage

import UniformActualCalendarNativeRectangle

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRectangleDataBank
noncomputable section
open UniformActualCalendarTypedSlots UniformActualCalendarRectangleProduced
open UniformLocalRectangleDescriptors UniformJointAllocation UniformAllAxisSeedPreparation
open UniformCanonicalCacheSlotGeometry UniformCanonicalSelectedPhase

def castBank {B:ℕ}{c:Header.Parameters}{q:Row}{ha he bank bank' positive j s}
 (eq:bank=bank')(data:Data (B:=B) c q ha he bank positive j s):
 Data (B:=B) c q ha he bank' positive j s where
 slot:=data.slot
 witness:=data.witness
 layout:=data.layout
 broadcast:=data.broadcast
 contents:=by rw[←eq];exact data.contents

lemma castBank_event {B:ℕ}{c:Header.Parameters}{q:Row}{ha he bank bank' positive j s}
 (eq:bank=bank')(data:Data (B:=B) c q ha he bank positive j s)(elapsed:ℕ):
 (castBank eq data).event c q ha he bank' positive j s elapsed=
 data.event c q ha he bank positive j s elapsed:=by
 subst bank'
 rfl

variable (constants:Constants)(n:ℕ)(axisIndex:Fin (axisCount n))(q:Row)(k time j:ℕ)
 {B:ℕ}{s:UniformMachine.State}
 (ha:q.a≤UniformCrossHeightPreparationMachine.widthOf (context constants n axisIndex q k time).height)
 (he:q.e≤UniformCrossHeightPreparationMachine.widthOf (context constants n axisIndex q k time).height)
 (positive:2≤(context constants n axisIndex q k time).ambient)

abbrev producerBank:=UniformLocalRectangleCacheBindings.coefficientBank axisIndex q
 (UniformJointCacheWorkspace.original n q) (context constants n axisIndex q k time)

def nativeData (data:Data (B:=B) (context constants n axisIndex q k time) q ha he
 (producerBank constants n axisIndex q k time) positive j s):
 Data (B:=B) (context constants n axisIndex q k time) q ha he
 (rowBank q (OAI.ExactFourier.NewtonFourier.invH (OAI.ExactFourier.zeta (radix n axisIndex)))) positive j s:=
 castBank (UniformActualCalendarCoefficientBank.context_bank constants n axisIndex q k time) data

lemma nativeData_event (data:Data (B:=B) (context constants n axisIndex q k time) q ha he
 (producerBank constants n axisIndex q k time) positive j s)(elapsed:ℕ):
 (nativeData constants n axisIndex q k time j ha he positive data).event _ _ _ _ _ _ _ _ elapsed=
 data.event _ _ _ _ _ _ _ _ elapsed:=
 castBank_event (UniformActualCalendarCoefficientBank.context_bank constants n axisIndex q k time) data elapsed

end
end ExactFourierCircuits.UniformActualCalendarRectangleDataBank

import UniformActualCalendarWitnessSlots

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarWitnessSource
open UniformActualCalendarTypedSlots UniformActualCalendarLocalSources
open UniformLocalCacheSlotConductorMachine (SlotWitness)
open UniformLocalFactorDispatchMachine (BroadcastLayout)
noncomputable section
variable {B : ℕ} (c : Header.Parameters) (q : UniformLocalRectangleDescriptors.Row)
 (slot : UniformLocalCacheChronology.Slot)
 (l : UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B)
 (bl : BroadcastLayout c q B)
 (ha : q.a≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (he : q.e≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (bank : Fin (UniformToeplitzCrossDAG.bankSize c.height.K)→ℂ)

def source {j : ℕ} (positive : 0<q.e) (h : SlotWitness c.height.K j slot)
 (broadcast : slot.broadcast=false) (extent : q.offset+q.width≤c.ambient)
 (elapsed : ℕ) (p : UniformGlobalMatchingScaleMachine.Phase) :
 Source (UniformActualCalendarRectangleEvent.actualEvent c q slot l bl ha he bank elapsed p)
  (UniformGlobalCalendarMatchingPhase.phaseSnapshot bank
   (typedSlot c q slot (8*c.height.K+6) l ha he positive
    (UniformActualCalendarWitnessSlots.stored c q slot ha he h))
   (typedSlot_matching c q slot (8*c.height.K+6) l ha he positive
    (UniformActualCalendarWitnessSlots.stored c q slot ha he h)
    (UniformActualCalendarWitnessSlots.matching c q slot ha he h)) p)
  (UniformChunkPortMachine.intervalEmbedding c.ambient q.offset q.width extent):=by
 have dc:=UniformReplaySlotWitness.depth_color h
 cases inverse:slot.inverse
 · exact UniformActualCalendarRectangleEvent.forward_source c q slot l bl ha he bank
    (8*c.height.K+6) positive (UniformActualCalendarWitnessSlots.stored c q slot ha he h)
    (UniformActualCalendarWitnessSlots.matching c q slot ha he h)
    dc.1 dc.2 broadcast inverse extent elapsed p
 · exact UniformActualCalendarRectangleEvent.inverse_source c q slot l bl ha he bank
    (8*c.height.K+6) positive (UniformActualCalendarWitnessSlots.stored c q slot ha he h)
    (UniformActualCalendarWitnessSlots.matching c q slot ha he h)
    dc.1 dc.2 broadcast inverse extent elapsed p

end
end ExactFourierCircuits.UniformActualCalendarWitnessSource

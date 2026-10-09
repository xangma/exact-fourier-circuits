import UniformActualCalendarBroadcastSource
import UniformActualCalendarWitnessSource

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRectangleSnapshot
open UniformActualCalendarTypedSlots UniformActualCalendarLocalSources
open UniformLocalCacheSlotConductorMachine (SlotWitness)
open UniformLocalFactorDispatchMachine (BroadcastLayout)
open UniformLayerSnapshot
noncomputable section
variable {B : ℕ} (c : Header.Parameters) (q : UniformLocalRectangleDescriptors.Row)
 (slot : UniformLocalCacheChronology.Slot)
 (l : UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B)
 (bl : BroadcastLayout c q B)
 (ha : q.a≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (he : q.e≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (bank : Fin (UniformToeplitzCrossDAG.bankSize c.height.K)→ℂ)

def snapshot {j : ℕ} (positive : 0<q.e) (h : SlotWitness c.height.K j slot)
 (gates : c.gates=UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height)
 (p : UniformGlobalMatchingScaleMachine.Phase) : Snapshot (Fin q.width):=
 if broadcast:slot.broadcast then
  UniformGlobalCalendarMatchingPhase.phaseSnapshot bank
   (UniformActualCalendarBroadcastSource.typed c q slot l bl ha he positive h gates broadcast)
   (UniformActualCalendarBroadcastSource.typed_matching c q slot l bl ha he positive h gates broadcast) p
 else
  UniformGlobalCalendarMatchingPhase.phaseSnapshot bank
   (typedSlot c q slot (8*c.height.K+6) l ha he positive
    (UniformActualCalendarWitnessSlots.stored c q slot ha he h))
   (typedSlot_matching c q slot (8*c.height.K+6) l ha he positive
    (UniformActualCalendarWitnessSlots.stored c q slot ha he h)
    (UniformActualCalendarWitnessSlots.matching c q slot ha he h)) p

/-- All three actual dispatcher branches supply a single explicit ordered
snapshot from the real slot witness and native row/factor producers. -/
def source {j : ℕ} (positive : 0<q.e) (h : SlotWitness c.height.K j slot)
 (gates : c.gates=UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height)
 (extent : q.offset+q.width≤c.ambient) (elapsed : ℕ) (p : UniformGlobalMatchingScaleMachine.Phase) :
 Source (UniformActualCalendarRectangleEvent.actualEvent c q slot l bl ha he bank elapsed p)
  (snapshot c q slot l bl ha he bank positive h gates p)
  (UniformChunkPortMachine.intervalEmbedding c.ambient q.offset q.width extent):=by
 by_cases broadcast:slot.broadcast=true
 · rw[snapshot,dite_eq_left broadcast]
   exact UniformActualCalendarBroadcastSource.source c q slot l bl ha he bank
    positive h gates broadcast extent elapsed p
 · rw[snapshot,dite_eq_right broadcast]
   have noBroadcast:slot.broadcast=false:=by cases eq:slot.broadcast <;>simp_all
   exact UniformActualCalendarWitnessSource.source c q slot l bl ha he bank
    positive h noBroadcast extent elapsed p

/-- The genuine cache/controller binding proves the only gate-count identity
used above; no output, action, or generated-snapshot premise is supplied. -/
def source_of_bindings {j : ℕ} (positive : 0<q.e) (h : SlotWitness c.height.K j slot)
 {original : UniformSeedHeightPreparation.Config} {D A dest FD FF FU FJ : ℕ}
 (binding : UniformLocalRectangleCacheBindings.Bindings c q original D A dest FD FF FU FJ)
 (extent : q.offset+q.width≤c.ambient) (elapsed : ℕ) (p : UniformGlobalMatchingScaleMachine.Phase) :
 Source (UniformActualCalendarRectangleEvent.actualEvent c q slot l bl ha he bank elapsed p)
  (snapshot c q slot l bl ha he bank positive h
   (UniformActualCalendarBroadcastSlots.actual_gates c q slot binding) p)
  (UniformChunkPortMachine.intervalEmbedding c.ambient q.offset q.width extent):=
 source c q slot l bl ha he bank positive h
  (UniformActualCalendarBroadcastSlots.actual_gates c q slot binding) extent elapsed p

end
end ExactFourierCircuits.UniformActualCalendarRectangleSnapshot

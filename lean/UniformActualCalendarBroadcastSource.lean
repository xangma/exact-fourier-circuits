import UniformActualCalendarBroadcastSlots

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarBroadcastSource
open UniformReplayPrint UniformToeplitzChunkWord UniformActualCalendarTypedSlots
open UniformDAGLayers (relabelCode)
open UniformActualCalendarLocalSources UniformLocalCacheChronology
open UniformLocalFactorDispatchMachine (BroadcastLayout)
open UniformLocalCacheSlotConductorMachine (SlotWitness)
namespace S
export UniformActualCalendarBroadcastSlots (codes stored matching)
end S
noncomputable section
variable {B : ℕ} (c : Header.Parameters) (q : UniformLocalRectangleDescriptors.Row) (slot : Slot)
 (l : UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B)
 (bl : BroadcastLayout c q B)
 (ha : q.a≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (he : q.e≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (bank : Fin (UniformToeplitzCrossDAG.bankSize c.height.K)→ℂ)

def placement : Placement q.e c.gates q.a q.width:=
 placementOfFit (UniformChunkPortMachine.intervalEmbedding q.width q.j0 q.e bl.sourceRange)
  (UniformChunkPortMachine.intervalEmbedding q.width q.i0 q.a bl.targetRange)
  (UniformBorrowedCoordinateBridge.interval_separated bl.sourceRange bl.targetRange l.chunk.separated)
  (by have:=bl.capacity;omega)

include ha he in
def typed {j : ℕ} (positive : 0<q.e) (h : SlotWitness c.height.K j slot)
 (gates : c.gates=UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height)
 (broadcast : slot.broadcast=true) :
 List (ShearCode (Fin q.width) (UniformToeplitzCrossDAG.bankSize c.height.K)):=
 (packList positive (S.codes c q slot bl) (S.stored c q slot bl ha he h gates broadcast)).map
  (relabelCode (placement c q slot l bl).embedding)

theorem typed_matching {j : ℕ} (positive : 0<q.e) (h : SlotWitness c.height.K j slot)
 (gates : c.gates=UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height)
 (broadcast : slot.broadcast=true) :
 Matching (typed c q slot l bl ha he positive h gates broadcast):=
 matching_relabel _ _ (packList_matching positive _ _ (S.matching c q slot bl ha he h gates broadcast))

theorem occurrences {j : ℕ} (positive : 0<q.e) (h : SlotWitness c.height.K j slot)
 (gates : c.gates=UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height)
 (broadcast : slot.broadcast=true) :
 UniformActualCalendarRectangleEvent.occurrences c q slot l bl ha he bank=
 UniformActualCalendarPackedCodes.values q.offset bank (typed c q slot l bl ha he positive h gates broadcast):=by
 refine (UniformActualCalendarRectangleEvent.occurrences_broadcast c q slot l bl ha he bank broadcast).trans ?_
 refine (UniformActualCalendarBroadcastCodes.occurrences_entries q slot c.gates c.height.P
  bl.capacity bl.outputCount bank).trans ?_
 symm
 have same:=UniformActualCalendarPackedCodes.canonical_values bl.sourceRange bl.targetRange
  l.chunk.separated bl.capacity positive q.offset bank (S.codes c q slot bl)
  (S.stored c q slot bl ha he h gates broadcast)
 exact same

/-- Actual signed broadcast rows determine ordered calls and all factors.
Inverse row reversal is handled at the local matrix boundary. -/
def source {j : ℕ} (positive : 0<q.e) (h : SlotWitness c.height.K j slot)
 (gates : c.gates=UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height)
 (broadcast : slot.broadcast=true) (extent : q.offset+q.width≤c.ambient)
 (elapsed : ℕ) (p : UniformGlobalMatchingScaleMachine.Phase) :
 Source (UniformActualCalendarRectangleEvent.actualEvent c q slot l bl ha he bank elapsed p)
  (UniformGlobalCalendarMatchingPhase.phaseSnapshot bank
   (typed c q slot l bl ha he positive h gates broadcast)
   (typed_matching c q slot l bl ha he positive h gates broadcast) p)
  (UniformChunkPortMachine.intervalEmbedding c.ambient q.offset q.width extent):=by
 apply UniformActualCalendarRectangleEvent.source c q slot l bl ha he bank _ _ bank _ ?_ elapsed p
 exact occurrences c q slot l bl ha he bank positive h gates broadcast

end
end ExactFourierCircuits.UniformActualCalendarBroadcastSource

import UniformActualCalendarTypedSlots

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRectangleEvent
open UniformMachine UniformLocalFactorDispatchMachine UniformLocalCacheSlotConductorMachine
open UniformReplayPrint UniformToeplitzChunkWord UniformDAGLayers
open UniformActualCalendarLocalSources
noncomputable section
variable {B : ℕ} (c : Header.Parameters) (q : UniformLocalRectangleDescriptors.Row)
 (slot : UniformLocalCacheChronology.Slot)
 (l : UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B)
 (bl : BroadcastLayout c q B)
 (ha : q.a≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (he : q.e≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (bank : Fin (UniformToeplitzCrossDAG.bankSize c.height.K)→ℂ)

/-- Once the actual replay slot has been identified, its genuine printer
occurrences determine the local snapshot's ordered calls and diagonal. -/
def source {R v : ℕ} (W : List (ShearCode (Fin v) R)) (hm : Matching W)
 (valuesBank : Fin R→ℂ) (band : Fin v ↪ Fin c.ambient)
 (occurrencesEq : occurrences c q slot l bl ha he bank=
   UniformActualCalendarOccurrences.typed valuesBank W band)
 (elapsed : ℕ) (p : UniformGlobalMatchingScaleMachine.Phase) :
 Source (actualEvent c q slot l bl ha he bank elapsed p)
  (UniformGlobalCalendarMatchingPhase.phaseSnapshot valuesBank W hm p) band:=by
 have geo:=dispatched_geometry c q slot l bl ha he
 have matching:=UniformGlobalMatchingScaleBankBridge.rowEdges_matching
  (printedRows c q slot l bl ha he) geo.2.1 geo.2.2
 have range:=UniformGlobalMatchingScaleBankBridge.rowEdges_range c.ambient
  (printedRows c q slot l bl ha he) geo.2.1 geo.1
 have capacity: (printedRows c q slot l bl ha he).length≤c.ambient:=by
  have h:=UniformMatchingAxisTableMachine.matching_capacity c.ambient
   (edges c q slot l bl ha he) matching range
  omega
 have same:values c q slot l bl ha he bank=
  fun lane i=>UniformGlobalMatchingScaleBankBridge.nativeFactor
   (edges c q slot l bl ha he) (coefficients c q slot l bl ha he bank) lane i.val:=by
  funext lane i
  exact values_native c q slot l bl ha he bank lane i
 unfold actualEvent
 rw[same]
 exact UniformActualCalendarOccurrences.source (edges c q slot l bl ha he)
  (coefficients c q slot l bl ha he bank) matching capacity valuesBank W hm band occurrencesEq p

namespace T
abbrev slotCodes := UniformActualCalendarTypedSlots.slotCodes
abbrev typedSlot := @UniformActualCalendarTypedSlots.typedSlot
abbrev typedSlot_matching := @UniformActualCalendarTypedSlots.typedSlot_matching
end T

/-- Forward actual rows and coefficients supply the local typed snapshot;
there is no endpoint, lane, or desired snapshot equality premise. -/
def forward_source (H : ℕ) (positive : 0<q.e)
 (stored : ∀code∈T.slotCodes c q slot H ha he,Stored q.e
   (UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height) q.a code)
 (matching : UniformDAGLayers.Matching (T.slotCodes c q slot H ha he))
 (depth : slot.depth≤H) (color : slot.color<11)
 (broadcast : slot.broadcast=false) (inverse : slot.inverse=false)
 (extent : q.offset+q.width≤c.ambient) (elapsed : ℕ) (p : UniformGlobalMatchingScaleMachine.Phase) :
 Source (actualEvent c q slot l bl ha he bank elapsed p)
  (UniformGlobalCalendarMatchingPhase.phaseSnapshot bank
   (T.typedSlot c q slot H l ha he positive stored)
   (T.typedSlot_matching c q slot H l ha he positive stored matching) p)
  (UniformChunkPortMachine.intervalEmbedding c.ambient q.offset q.width extent):=by
 refine source c q slot l bl ha he bank _ _ bank _ ?_ elapsed p
 refine (occurrences_forward c q slot l bl ha he bank broadcast inverse).trans ?_
 exact UniformActualCalendarTypedSlots.forward c q slot H l ha he bank positive stored depth color broadcast inverse

def inverse_source (H : ℕ) (positive : 0<q.e)
 (stored : ∀code∈T.slotCodes c q slot H ha he,Stored q.e
   (UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height) q.a code)
 (matching : UniformDAGLayers.Matching (T.slotCodes c q slot H ha he))
 (depth : slot.depth≤H) (color : slot.color<11)
 (broadcast : slot.broadcast=false) (inverse : slot.inverse=true)
 (extent : q.offset+q.width≤c.ambient) (elapsed : ℕ) (p : UniformGlobalMatchingScaleMachine.Phase) :
 Source (actualEvent c q slot l bl ha he bank elapsed p)
  (UniformGlobalCalendarMatchingPhase.phaseSnapshot bank
   (T.typedSlot c q slot H l ha he positive stored)
   (T.typedSlot_matching c q slot H l ha he positive stored matching) p)
  (UniformChunkPortMachine.intervalEmbedding c.ambient q.offset q.width extent):=by
 refine source c q slot l bl ha he bank _ _ bank _ ?_ elapsed p
 refine (occurrences_inverse c q slot l bl ha he bank broadcast inverse).trans ?_
 exact UniformActualCalendarTypedSlots.inverse c q slot H l ha he bank positive stored depth color broadcast inverse

end
end ExactFourierCircuits.UniformActualCalendarRectangleEvent

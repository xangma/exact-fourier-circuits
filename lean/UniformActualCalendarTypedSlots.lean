import UniformActualCalendarRectangleOccurrences
import UniformMatchingCoordinateBridge

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarTypedSlots
open UniformReplayPrint UniformToeplitzChunkWord UniformDAGLayers UniformChunkPortMachine
noncomputable section

def placement {B : ℕ} (p : UniformChunkMatchingPreparation.Parameters)
 (l : UniformChunkMatchingPreparation.Layout p B) :=
 placementOfFit (g:=UniformCrossHeightPreparationMachine.gates p.height)
  (intervalEmbedding p.radix p.source p.height.e l.sourceRange)
  (intervalEmbedding p.radix p.target p.height.a l.targetRange)
  (UniformBorrowedCoordinateBridge.interval_separated l.sourceRange l.targetRange l.separated)
  (by have:=l.capacity;omega)

theorem producer_values {B R : ℕ} (p : UniformChunkMatchingPreparation.Parameters)
 (l : UniformChunkMatchingPreparation.Layout p B) (positive : 0<p.height.e)
 (offset : ℕ) (bank : Fin R→ℂ) (W : List (ShearCode ℕ R))
 (stored : ∀code∈W,Stored p.height.e (UniformCrossHeightPreparationMachine.gates p.height) p.height.a code) :
 UniformActualCalendarPackedCodes.values offset bank
   ((packList positive W stored).map (relabelCode (placement p l).embedding))=
 W.map (fun code=>(offset+UniformChunkMatchingPreparation.coordinate p l.capacity code.dst,
  offset+UniformChunkMatchingPreparation.coordinate p l.capacity code.src,code.coefficient.eval bank)):=
 UniformActualCalendarPackedCodes.canonical_values l.sourceRange l.targetRange l.separated l.capacity
  positive offset bank W stored

namespace Header
abbrev Parameters := UniformLocalCacheSlotHeaderMachine.Parameters
abbrev forward := UniformLocalCacheSlotHeaderMachine.forward
end Header
open UniformLocalCacheChronology
variable {B : ℕ} (c : Header.Parameters) (q : UniformLocalRectangleDescriptors.Row)
 (slot : Slot) (H : ℕ)
 (l : UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B)
 (ha : q.a≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (he : q.e≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (bank : Fin (UniformToeplitzCrossDAG.bankSize c.height.K)→ℂ)

def slotCodes := layer (UniformToeplitzCrossDAG.crossDAG c.height.K q.a q.e ha he) H slot

def typedSlot (positive : 0<q.e)
 (stored : ∀code∈slotCodes c q slot H ha he,Stored q.e
   (UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height) q.a code) :
 List (ShearCode (Fin q.width) (UniformToeplitzCrossDAG.bankSize c.height.K)) :=
 (packList positive (slotCodes c q slot H ha he) stored).map
  (relabelCode (placement (Header.forward c q slot).chunk l.chunk).embedding)

theorem typedSlot_matching (positive : 0<q.e)
 (stored : ∀code∈slotCodes c q slot H ha he,Stored q.e
   (UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height) q.a code)
 (matching : UniformDAGLayers.Matching (slotCodes c q slot H ha he)) :
 Matching (typedSlot c q slot H l ha he positive stored):=
 matching_relabel _ _ (packList_matching positive _ stored matching)

/-- Actual selected forward occurrences equal the canonical typed replay
slot's physical endpoint/coefficient values. -/
theorem forward (positive : 0<q.e)
 (stored : ∀code∈slotCodes c q slot H ha he,Stored q.e
   (UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height) q.a code)
 (depth : slot.depth≤H) (color : slot.color<11)
 (broadcast : slot.broadcast=false) (inverse : slot.inverse=false) :
 UniformActualCalendarForwardCodes.occurrences (Header.forward c q slot) l ha he bank=
 UniformActualCalendarPackedCodes.values q.offset bank (typedSlot c q slot H l ha he positive stored):=by
 refine (UniformActualCalendarHeaderCodes.forward c q slot H l ha he bank depth color broadcast inverse).trans ?_
 exact (producer_values (Header.forward c q slot).chunk l.chunk positive q.offset bank
  (slotCodes c q slot H ha he) stored).symm

theorem inverse (positive : 0<q.e)
 (stored : ∀code∈slotCodes c q slot H ha he,Stored q.e
   (UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height) q.a code)
 (depth : slot.depth≤H) (color : slot.color<11)
 (broadcast : slot.broadcast=false) (inverse : slot.inverse=true) :
 UniformActualCalendarInverseCodes.occurrences (Header.forward c q slot) l ha he bank=
 UniformActualCalendarPackedCodes.values q.offset bank (typedSlot c q slot H l ha he positive stored):=by
 refine (UniformActualCalendarHeaderCodes.inverse c q slot H l ha he bank depth color broadcast inverse).trans ?_
 exact (producer_values (Header.forward c q slot).chunk l.chunk positive q.offset bank
  (slotCodes c q slot H ha he) stored).symm

end
end ExactFourierCircuits.UniformActualCalendarTypedSlots

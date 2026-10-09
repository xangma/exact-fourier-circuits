import UniformActualCalendarInverseCodes

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarHeaderCodes
open UniformReplayPrint UniformLocalCacheChronology
namespace Header
abbrev Parameters := UniformLocalCacheSlotHeaderMachine.Parameters
abbrev forward := UniformLocalCacheSlotHeaderMachine.forward
end Header
noncomputable section
variable {B : ℕ} (c : Header.Parameters) (q : UniformLocalRectangleDescriptors.Row)
 (slot : Slot) (H : ℕ)
 (l : UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B)
 (ha : q.a≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (he : q.e≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (bank : Fin (UniformToeplitzCrossDAG.bankSize c.height.K)→ℂ)

def occurrenceValue (code : ShearCode ℕ (UniformToeplitzCrossDAG.bankSize c.height.K)) :
 Nat × (Nat × Complex) :=
 (q.offset+UniformChunkMatchingPreparation.coordinate (Header.forward c q slot).chunk l.chunk.capacity code.dst,
  q.offset+UniformChunkMatchingPreparation.coordinate (Header.forward c q slot).chunk l.chunk.capacity code.src,
  code.coefficient.eval bank)

/-- Actual forward headers select precisely the replay slot's stable depth and
color occurrences. No word equality is supplied as an input. -/
theorem forward (depth : slot.depth≤H) (color : slot.color<11)
 (broadcast : slot.broadcast=false) (inverse : slot.inverse=false) :
 UniformActualCalendarForwardCodes.occurrences (Header.forward c q slot) l ha he bank=
 (layer (UniformToeplitzCrossDAG.crossDAG c.height.K q.a q.e ha he) H slot).map
  (occurrenceValue c q slot l bank):=by
 refine (UniformActualCalendarForwardCodes.occurrences_color (Header.forward c q slot) l ha he bank color).trans ?_
 rw[UniformActualCalendarForwardCodes.layer_forward _ _ _ depth color broadcast inverse]
 rw[UniformCalendarSelectedColors.chosen_eq_color _ _ color]
 rfl

/-- The inverse producer uses the same literal slot with reversed occurrences
and negated selected coefficients. -/
theorem inverse (depth : slot.depth≤H) (color : slot.color<11)
 (broadcast : slot.broadcast=false) (inverse : slot.inverse=true) :
 UniformActualCalendarInverseCodes.occurrences (Header.forward c q slot) l ha he bank=
 (layer (UniformToeplitzCrossDAG.crossDAG c.height.K q.a q.e ha he) H slot).map
  (occurrenceValue c q slot l bank):=by
 refine (UniformActualCalendarInverseCodes.occurrences_color (Header.forward c q slot) l ha he bank color).trans ?_
 simp only[layer,broadcast,inverse,Bool.false_eq_true,ite_false,ite_true]
 rw[UniformCalendarStableDepth.bucket_at _ slot.enabled H slot.depth depth]
 rfl

end
end ExactFourierCircuits.UniformActualCalendarHeaderCodes

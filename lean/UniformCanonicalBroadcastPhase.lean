import UniformCanonicalPairPhase
import UniformActualCalendarBroadcastReverse

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCanonicalBroadcastPhase
noncomputable section
open OAI.ExactFourier UniformToeplitzChunkWord UniformLocalFourierLayers
open UniformActualCalendarTypedSlots UniformActualCalendarWitnessSlots
open UniformGlobalCalendarMatchingPhase UniformGlobalMatchingScaleMachine
open UniformLocalFactorDispatchMachine (BroadcastLayout)
open UniformLocalCacheSlotConductorMachine (SlotWitness)
open UniformCanonicalMatchingPhase UniformCanonicalRectanglePhase
open UniformCalendarRenderTick

variable {B : ℕ} (c : Header.Parameters) (q : UniformLocalRectangleDescriptors.Row)
 (slot : UniformLocalCacheChronology.Slot)
 (l : UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B)
 (bl : BroadcastLayout c q B)
 (ha : q.a≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (he : q.e≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (bank : Fin (UniformToeplitzCrossDAG.bankSize c.height.K)→ℂ)

/-- The real ascending broadcast printer represents the normal signed slot;
its inverse occurrence order is handled by the proved phase permutation. -/
theorem normal_phase {j : ℕ} (positive : 0<q.e) (h : SlotWitness c.height.K j slot)
 (gates : c.gates=UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height)
 (broadcast : slot.broadcast=true) (p : Phase) :
 (phaseSnapshot bank (UniformActualCalendarBroadcastSource.typed c q slot l bl ha he positive h gates broadcast)
  (UniformActualCalendarBroadcastSource.typed_matching c q slot l bl ha he positive h gates broadcast) p).matrix=
 (phaseSnapshot bank (typedSlot c q slot (8*c.height.K+6) l ha he positive (stored c q slot ha he h))
  (typedSlot_matching c q slot (8*c.height.K+6) l ha he positive (stored c q slot ha he h)
   (matching c q slot ha he h)) p).matrix:=by
 have eq:=UniformActualCalendarBroadcastReverse.normal_typed c q slot l bl ha he positive h gates broadcast
 have hm:=typedSlot_matching c q slot (8*c.height.K+6) l ha he positive
  (stored c q slot ha he h) (matching c q slot ha he h)
 have actual:=UniformActualCalendarBroadcastSource.typed_matching c q slot l bl ha he positive h gates broadcast
 cases inverse:slot.inverse
 · simp only [inverse,Bool.false_eq_true,ite_false] at eq
   exact (phase_congr bank eq hm actual p).symm
 · simp only [inverse,ite_true] at eq
   have hr : Matching (UniformActualCalendarBroadcastSource.typed c q slot l bl ha he positive h gates broadcast).reverse:=
    Eq.mp (congrArg Matching eq) hm
   exact (phase_reverse bank _ actual hr p).symm.trans (phase_congr bank eq hm hr p).symm

/-- Exact physically ordered broadcast snapshot at the actual chunk tick. -/
theorem chunk_tick {j : ℕ} (positive : 0<q.e) (h : SlotWitness c.height.K j slot)
 (gates : c.gates=UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height)
 (broadcast : slot.broadcast=true) (p : Fin 28) :
 (phaseSnapshot bank (UniformActualCalendarBroadcastSource.typed c q slot l bl ha he positive h gates broadcast)
  (UniformActualCalendarBroadcastSource.typed_matching c q slot l bl ha he positive h gates broadcast)
  (phases.get ⟨p.val,by rw[phases_length];exact p.isLt⟩)).matrix=
 tick (chunkRender c q slot ha he l positive bank) (28*j+p.val):=
 (normal_phase c q slot l bl ha he bank positive h gates broadcast _).trans
  (chunk_slot_tick c q slot ha he l positive bank h p)

end
end ExactFourierCircuits.UniformCanonicalBroadcastPhase

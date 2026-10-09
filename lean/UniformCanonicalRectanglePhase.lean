import UniformActualCalendarWitnessSlots
import UniformCanonicalMatchingPhase

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCanonicalRectanglePhase
noncomputable section
open OAI.ExactFourier UniformToeplitzChunkWord UniformReplayPrint UniformLocalFourierLayers
open UniformGlobalCalendarMatchingPhase UniformGlobalCalendarPhases UniformGlobalMatchingScaleMachine
open UniformActualCalendarTypedSlots UniformActualCalendarWitnessSlots
open UniformLocalCacheSlotConductorMachine (SlotWitness)
open UniformCalendarRenderTick UniformCalendarRenderMatching

variable {B : ℕ} (c : Header.Parameters) (q : UniformLocalRectangleDescriptors.Row)
 (slot : UniformLocalCacheChronology.Slot)
 (ha : q.a≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (he : q.e≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (l : UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B)
 (positive : 0<q.e)
 (bank : Fin (UniformToeplitzCrossDAG.bankSize c.height.K)→ℂ)

/-- This is the real normal chunk render at the producer's canonical placement. -/
def chunkRender:=chunkSchedule (dag c q slot ha he) bank positive
 (normalPlacement c q slot ha he l) (dag_depth c q slot ha he) (by omega : 2≤6)
 (dag_fanout c q slot ha he)

/-- Actual cached slot ordinals, including signed inverse replay, select the
literal matching phase of the actual normal chunk render. -/
theorem chunk_slot_tick {j : ℕ} (h : SlotWitness c.height.K j slot) (p : Fin 28) :
 (phaseSnapshot bank
  (typedSlot c q slot (8*c.height.K+6) l ha he positive (stored c q slot ha he h))
  (typedSlot_matching c q slot (8*c.height.K+6) l ha he positive
   (stored c q slot ha he h) (matching c q slot ha he h))
  (phases.get ⟨p.val,by rw [phases_length];exact p.isLt⟩)).matrix=
 tick (chunkRender c q slot ha he l positive bank) (28*j+p.val):=by
 symm
 have get:=chunkSlots_get c q slot ha he l positive h
 have result:=matching_tick bank (chunkSlots c q slot ha he l positive)
  (chunkLayers_matching (dag c q slot ha he) positive (normalPlacement c q slot ha he l)
   (dag_depth c q slot ha he) (by omega : 2≤6) (dag_fanout c q slot ha he))
  ⟨j,chunkSlots_bound c q slot ha he l positive h⟩ p
 change tick (chunkRender c q slot ha he l positive bank) (28*j+p.val)=_ at result
 exact result.trans (UniformCanonicalMatchingPhase.phase_congr bank get _ _ _)

/-- The ordinary selector elapsed tick is used directly; no second reflection
or phase reversal is performed inside the selected cache entry. -/
theorem chunk_elapsed_tick (elapsed : ℕ)
 (h : SlotWitness c.height.K (elapsed/28) slot) :
 (phaseSnapshot bank
  (typedSlot c q slot (8*c.height.K+6) l ha he positive (stored c q slot ha he h))
  (typedSlot_matching c q slot (8*c.height.K+6) l ha he positive
   (stored c q slot ha he h) (matching c q slot ha he h))
  (phases.get ⟨elapsed%28,by rw [phases_length];exact Nat.mod_lt _ (by decide)⟩)).matrix=
 tick (chunkRender c q slot ha he l positive bank) elapsed:=by
 have time : 28*(elapsed/28)+elapsed%28=elapsed:=by omega
 simpa only [time] using chunk_slot_tick c q slot ha he l positive bank h
  ⟨elapsed%28,Nat.mod_lt _ (by decide)⟩

end
end ExactFourierCircuits.UniformCanonicalRectanglePhase

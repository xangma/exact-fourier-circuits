import UniformCanonicalBroadcastPhase
import UniformActualCalendarRectangleSnapshot

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCanonicalRectangleSnapshot
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformWorkspacePlanner UniformBalancedToeplitz
open UniformActualCalendarTypedSlots UniformActualCalendarWitnessSlots
open UniformGlobalMatchingScaleMachine UniformLocalFactorDispatchMachine
open UniformLocalCacheSlotConductorMachine (SlotWitness)
open UniformCanonicalRectanglePhase UniformCanonicalPairPhase UniformCanonicalSelectedPhase
open UniformCalendarRenderTick UniformCalendarRenderPlan
open UniformJointAllocation UniformAllAxisSeedPreparation UniformCanonicalCacheSlotGeometry

/-- The same explicit snapshot for which actual cached endpoints and native
factor sources have been proved now has its actual normal rendered tick. -/
theorem chunk_snapshot_tick {B : ℕ} (c : Header.Parameters) (q : UniformLocalRectangleDescriptors.Row)
 (slot : UniformLocalCacheChronology.Slot)
 (l : UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B)
 (bl : BroadcastLayout c q B)
 (ha : q.a≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (he : q.e≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (bank : Fin (UniformToeplitzCrossDAG.bankSize c.height.K)→ℂ)
 {j : ℕ} (positive : 0<q.e) (h : SlotWitness c.height.K j slot)
 (gates : c.gates=UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height)
 (p : Fin 28) :
 (UniformActualCalendarRectangleSnapshot.snapshot c q slot l bl ha he bank positive h gates
  (phases.get ⟨p.val,by rw[phases_length];exact p.isLt⟩)).matrix=
 tick (chunkRender c q slot ha he l positive bank) (28*j+p.val):=by
 by_cases broadcast:slot.broadcast=true
 · rw[UniformActualCalendarRectangleSnapshot.snapshot,dite_eq_left broadcast]
   exact UniformCanonicalBroadcastPhase.chunk_tick c q slot l bl ha he bank positive h gates broadcast p
 · rw[UniformActualCalendarRectangleSnapshot.snapshot,dite_eq_right broadcast]
   exact chunk_slot_tick c q slot ha he l positive bank h p

variable (constants : Constants) (n : ℕ) (axisIndex : Fin (axisCount n))
 (v o : ℕ) (hv : 0<selected v)
 (indices : Fin (chunkCount (v-v/2) (selected v))×Fin (chunkCount (v/2) (selected v)))
 (k time : ℕ) (slot : UniformLocalCacheChronology.Slot) {B : ℕ}
 (ha : (pairRow v o indices).a≤UniformCrossHeightPreparationMachine.widthOf
  (Header.forward (pairContext constants n axisIndex v o indices k time) (pairRow v o indices) slot).chunk.height)
 (he : (pairRow v o indices).e≤UniformCrossHeightPreparationMachine.widthOf
  (Header.forward (pairContext constants n axisIndex v o indices k time) (pairRow v o indices) slot).chunk.height)
 (l : UniformForwardMatchingFactorPreparation.Layout
  (Header.forward (pairContext constants n axisIndex v o indices k time) (pairRow v o indices) slot) B)
 (bl : BroadcastLayout (pairContext constants n axisIndex v o indices k time) (pairRow v o indices) B)

lemma pair_gates :
 (pairContext constants n axisIndex v o indices k time).gates=
 UniformCrossHeightPreparationMachine.gates
  (Header.forward (pairContext constants n axisIndex v o indices k time) (pairRow v o indices) slot).chunk.height:=rfl

/-- Concrete all-branch local matrix identity for the actual explicit cache
snapshot. Its only chronology input is the genuine stored slot witness. -/
theorem pair_snapshot_tick (f : PowerSeries ℂ) {j : ℕ}
 (h : SlotWitness (pairContext constants n axisIndex v o indices k time).height.K j slot)
 (p : Fin 28) :
 (UniformActualCalendarRectangleSnapshot.snapshot
  (pairContext constants n axisIndex v o indices k time) (pairRow v o indices) slot l bl ha he
  (rowBank (pairRow v o indices) f) (size_pos _ _ hv _) h
  (pair_gates constants n axisIndex v o indices k time slot)
  (phases.get ⟨p.val,by rw[phases_length];exact p.isLt⟩)).matrix=
 tick (pairPiece v hv o f indices).layers (28*j+p.val):=by
 have phase:=chunk_snapshot_tick
  (pairContext constants n axisIndex v o indices k time) (pairRow v o indices) slot l bl ha he
  (rowBank (pairRow v o indices) f) (size_pos _ _ hv _) h
  (pair_gates constants n axisIndex v o indices k time slot) p
 have render:=pair_chunkRender constants n axisIndex v o hv indices k time slot ha he l f
 exact phase.trans (congrArg (fun L=>tick L (28*j+p.val)) render)

/-- The selector's actual elapsed time uses its ordinary quotient and remainder. -/
theorem pair_snapshot_elapsed (f : PowerSeries ℂ) (elapsed : ℕ)
 (h : SlotWitness (pairContext constants n axisIndex v o indices k time).height.K (elapsed/28) slot) :
 (UniformActualCalendarRectangleSnapshot.snapshot
  (pairContext constants n axisIndex v o indices k time) (pairRow v o indices) slot l bl ha he
  (rowBank (pairRow v o indices) f) (size_pos _ _ hv _) h
  (pair_gates constants n axisIndex v o indices k time slot)
  (phases.get ⟨elapsed%28,by rw[phases_length];exact Nat.mod_lt _ (by decide)⟩)).matrix=
 tick (pairPiece v hv o f indices).layers elapsed:=by
 have clockEq : 28*(elapsed/28)+elapsed%28=elapsed:=by omega
 simpa only [clockEq] using pair_snapshot_tick constants n axisIndex v o hv indices k time slot ha he l bl f h
  ⟨elapsed%28,Nat.mod_lt _ (by decide)⟩

/-- The actual physical event has this same explicit snapshot as its ordered
source; no local Source is left as a caller-supplied premise. -/
def pair_snapshot_source (f : PowerSeries ℂ) {j : ℕ}
 (h : SlotWitness (pairContext constants n axisIndex v o indices k time).height.K j slot)
 (extent : (pairRow v o indices).offset+(pairRow v o indices).width≤
  (pairContext constants n axisIndex v o indices k time).ambient)
 (elapsed : ℕ) (p : Phase) :
 UniformActualCalendarLocalSources.Source
  (UniformActualCalendarRectangleEvent.actualEvent
   (pairContext constants n axisIndex v o indices k time) (pairRow v o indices) slot l bl ha he
   (rowBank (pairRow v o indices) f) elapsed p)
  (UniformActualCalendarRectangleSnapshot.snapshot
   (pairContext constants n axisIndex v o indices k time) (pairRow v o indices) slot l bl ha he
   (rowBank (pairRow v o indices) f) (size_pos _ _ hv _) h
   (pair_gates constants n axisIndex v o indices k time slot) p)
  (UniformChunkPortMachine.intervalEmbedding
   (pairContext constants n axisIndex v o indices k time).ambient
   (pairRow v o indices).offset (pairRow v o indices).width extent):=
 UniformActualCalendarRectangleSnapshot.source
  (pairContext constants n axisIndex v o indices k time) (pairRow v o indices) slot l bl ha he
  (rowBank (pairRow v o indices) f) (size_pos _ _ hv _) h
  (pair_gates constants n axisIndex v o indices k time slot) extent elapsed p

end
end ExactFourierCircuits.UniformCanonicalRectangleSnapshot

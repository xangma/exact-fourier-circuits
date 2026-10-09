import UniformActualCalendarCoefficientBank

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarShiftedSnapshot
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformBalancedToeplitz UniformWorkspacePlanner
open UniformActualCalendarTypedSlots UniformActualCalendarWitnessSlots
open UniformCanonicalRectanglePhase UniformCanonicalSelectedPhase UniformCanonicalPairPhase
open UniformJointAllocation UniformAllAxisSeedPreparation UniformCanonicalCacheSlotGeometry
open UniformActualCalendarShiftedPair UniformCalendarRenderTick UniformCalendarRenderPlan
open UniformGlobalMatchingScaleMachine UniformLocalFactorDispatchMachine
open UniformLocalCacheSlotConductorMachine (SlotWitness)

variable (constants:Constants)(n:ℕ)(axisIndex:Fin (axisCount n))(v o:ℕ)(hv:0<selected v)
 (indices:Fin (chunkCount (v-v/2) (selected v))×Fin (chunkCount (v/2) (selected v)))
 (k time j:ℕ)(slot:UniformLocalCacheChronology.Slot){B:ℕ}
 (ha:(pairRow v o indices).a≤UniformCrossHeightPreparationMachine.widthOf
  (Header.forward (shifted constants n axisIndex v o indices k time j) (pairRow v o indices) slot).chunk.height)
 (he:(pairRow v o indices).e≤UniformCrossHeightPreparationMachine.widthOf
  (Header.forward (shifted constants n axisIndex v o indices k time j) (pairRow v o indices) slot).chunk.height)
 (l:UniformForwardMatchingFactorPreparation.Layout
  (Header.forward (shifted constants n axisIndex v o indices k time j) (pairRow v o indices) slot) B)
 (bl:BroadcastLayout (shifted constants n axisIndex v o indices k time j) (pairRow v o indices) B)

lemma gates:
 (shifted constants n axisIndex v o indices k time j).gates=
 UniformCrossHeightPreparationMachine.gates
  (Header.forward (shifted constants n axisIndex v o indices k time j) (pairRow v o indices) slot).chunk.height:=rfl

theorem snapshot_tick (f:PowerSeries ℂ)
 (h:SlotWitness (shifted constants n axisIndex v o indices k time j).height.K j slot)(p:Fin 28):
 (UniformActualCalendarRectangleSnapshot.snapshot
  (shifted constants n axisIndex v o indices k time j) (pairRow v o indices) slot l bl ha he
  (rowBank (pairRow v o indices) f) (size_pos _ _ hv _) h
  (gates constants n axisIndex v o indices k time j slot)
  (phases.get ⟨p.val,by rw[phases_length];exact p.isLt⟩)).matrix=
 tick (pairPiece v hv o f indices).layers (28*j+p.val):=by
 have phase:=UniformCanonicalRectangleSnapshot.chunk_snapshot_tick
  (shifted constants n axisIndex v o indices k time j) (pairRow v o indices) slot l bl ha he
  (rowBank (pairRow v o indices) f) (size_pos _ _ hv _) h
  (gates constants n axisIndex v o indices k time j slot) p
 have render:=chunk_selected constants n axisIndex v o hv indices k time j slot ha he l f
 exact phase.trans (congrArg (fun L=>tick L (28*j+p.val)) render)

def snapshot_source (f:PowerSeries ℂ)
 (h:SlotWitness (shifted constants n axisIndex v o indices k time j).height.K j slot)
 (extent:(pairRow v o indices).offset+(pairRow v o indices).width≤
  (shifted constants n axisIndex v o indices k time j).ambient)
 (elapsed:ℕ)(p:Phase):
 UniformActualCalendarLocalSources.Source
  (UniformActualCalendarRectangleEvent.actualEvent
   (shifted constants n axisIndex v o indices k time j) (pairRow v o indices) slot l bl ha he
   (rowBank (pairRow v o indices) f) elapsed p)
  (UniformActualCalendarRectangleSnapshot.snapshot
   (shifted constants n axisIndex v o indices k time j) (pairRow v o indices) slot l bl ha he
   (rowBank (pairRow v o indices) f) (size_pos _ _ hv _) h
   (gates constants n axisIndex v o indices k time j slot) p)
  (UniformChunkPortMachine.intervalEmbedding
   (shifted constants n axisIndex v o indices k time j).ambient
   (pairRow v o indices).offset (pairRow v o indices).width extent):=
 UniformActualCalendarRectangleSnapshot.source
  (shifted constants n axisIndex v o indices k time j) (pairRow v o indices) slot l bl ha he
  (rowBank (pairRow v o indices) f) (size_pos _ _ hv _) h
  (gates constants n axisIndex v o indices k time j slot) extent elapsed p

end
end ExactFourierCircuits.UniformActualCalendarShiftedSnapshot

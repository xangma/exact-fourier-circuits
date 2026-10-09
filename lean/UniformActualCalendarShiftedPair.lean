import UniformCanonicalRectangleSnapshot
import UniformActualCalendarRectangleProduced

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarShiftedPair
noncomputable section
open OAI.ExactFourier UniformToeplitzChunkWord UniformReplayPrint UniformLocalFourierLayers
open UniformWorkspacePlanner UniformBalancedToeplitz UniformLocalRectangleDescriptors
open UniformActualCalendarTypedSlots UniformActualCalendarWitnessSlots
open UniformCanonicalRectanglePhase UniformCanonicalSelectedPhase UniformCanonicalPairPhase
open UniformJointAllocation UniformAllAxisSeedPreparation UniformCanonicalCacheSlotGeometry
open UniformCalendarRenderTick UniformCalendarRenderPlan

lemma placement_fit {B:ℕ}(c:Header.Parameters)(q:Row)(slot:UniformLocalCacheChronology.Slot)
 (ha:q.a≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (he:q.e≤UniformCrossHeightPreparationMachine.widthOf (Header.forward c q slot).chunk.height)
 (l:UniformForwardMatchingFactorPreparation.Layout (Header.forward c q slot) B):
 normalPlacement c q slot ha he l=
 placementOfFit (g:=(dag c q slot ha he).size)
  (UniformChunkPortMachine.intervalEmbedding q.width q.j0 q.e l.chunk.sourceRange)
  (UniformChunkPortMachine.intervalEmbedding q.width q.i0 q.a l.chunk.targetRange)
  (UniformBorrowedCoordinateBridge.interval_separated l.chunk.sourceRange l.chunk.targetRange l.chunk.separated)
  (by
    rw [UniformActualCalendarWitnessSlots.size]
    have fit := l.chunk.capacity
    change UniformCrossHeightPreparationMachine.gates (Header.forward c q slot).chunk.height+q.e+q.a≤q.width at fit
    omega):=by
 unfold normalPlacement placement
 exact castPlacement_fit _ _ _ _ _ _

variable (constants:Constants)(n:ℕ)(axisIndex:Fin (axisCount n))(v o:ℕ)(hv:0<selected v)
 (indices:Fin (chunkCount (v-v/2) (selected v))×Fin (chunkCount (v/2) (selected v)))
 (k time j:ℕ)(slot:UniformLocalCacheChronology.Slot){B:ℕ}
abbrev shifted:=UniformLocalCacheSlotConductorMachine.Cursor.shifted
 (pairContext constants n axisIndex v o indices k time) j
variable
 (ha:(pairRow v o indices).a≤UniformCrossHeightPreparationMachine.widthOf
  (Header.forward (shifted constants n axisIndex v o indices k time j) (pairRow v o indices) slot).chunk.height)
 (he:(pairRow v o indices).e≤UniformCrossHeightPreparationMachine.widthOf
  (Header.forward (shifted constants n axisIndex v o indices k time j) (pairRow v o indices) slot).chunk.height)
 (l:UniformForwardMatchingFactorPreparation.Layout
  (Header.forward (shifted constants n axisIndex v o indices k time j) (pairRow v o indices) slot) B)

/-- Advancing physical pool/control/ABI cursors does not change the actual
chunk's normal DAG, borrowed placement, or rank kernels. -/
theorem chunk_selected (f:PowerSeries ℂ):
 chunkRender (shifted constants n axisIndex v o indices k time j) (pairRow v o indices) slot ha he l
  (size_pos _ _ hv _) (rowBank (pairRow v o indices) f)=pairSchedule v hv f indices:=by
 unfold chunkRender
 rw[placement_fit]
 change selectedSchedule hv (size_mem _ _ indices.1) (size_mem _ _ indices.2)
  (UniformChunkPortMachine.intervalEmbedding v _ _ l.chunk.sourceRange)
  (UniformChunkPortMachine.intervalEmbedding v _ _ l.chunk.targetRange)
  (UniformBorrowedCoordinateBridge.interval_separated l.chunk.sourceRange l.chunk.targetRange l.chunk.separated)
  (rowBank (pairRow v o indices) f)=_
 apply selected_congr
 · exact (pairSource_interval v hv indices.2 l.chunk.sourceRange).symm
 · exact (pairTarget_interval v hv indices.1 l.chunk.targetRange).symm

end
end ExactFourierCircuits.UniformActualCalendarShiftedPair

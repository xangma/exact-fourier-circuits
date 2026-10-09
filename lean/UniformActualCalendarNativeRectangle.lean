import UniformCalendarNativePieces

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarNativeRectangle
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformBalancedToeplitz UniformWorkspacePlanner
open UniformJointAllocation UniformAllAxisSeedPreparation UniformCanonicalCacheSlotGeometry
open UniformCanonicalSelectedPhase UniformCanonicalPairPhase UniformActualCalendarShiftedPair
open UniformLocalCacheTiming UniformCalendarNativePieces UniformCalendarRenderTick
open UniformActualCalendarTypedSlots UniformActualCalendarRectangleProduced
open UniformGlobalMatchingScaleMachine

lemma forward_width (c:Header.Parameters)(q:UniformLocalRectangleDescriptors.Row)
 (slot:UniformLocalCacheChronology.Slot)(j:ℕ):
 UniformCrossHeightPreparationMachine.widthOf
  (Header.forward (UniformLocalCacheSlotConductorMachine.Cursor.shifted c j) q slot).chunk.height=
 UniformCrossHeightPreparationMachine.widthOf c.height:=rfl

lemma positive {f:PowerSeries ℂ}{hf:PowerSeries.constantCoeff f≠0}
 {q:UniformLocalRectangleDescriptors.Row}{L:List (Layer q.width)}
 (actual:Core f hf (.rectangle q) L):0<q.e:=by
 cases actual with
 | pair v o hv indices=>exact size_pos _ _ hv indices.2

variable (constants:Constants)(n:ℕ)(axisIndex:Fin (axisCount n))
 (q:UniformLocalRectangleDescriptors.Row)(k time j:ℕ){B:ℕ}{s:UniformMachine.State}
 (ha:q.a≤UniformCrossHeightPreparationMachine.widthOf (context constants n axisIndex q k time).height)
 (he:q.e≤UniformCrossHeightPreparationMachine.widthOf (context constants n axisIndex q k time).height)
 (ambient:2≤(context constants n axisIndex q k time).ambient)
 (f:PowerSeries ℂ)
 (data:Data (B:=B) (context constants n axisIndex q k time) q ha he (rowBank q f) ambient j s)

lemma gates:
 (UniformLocalCacheSlotConductorMachine.Cursor.shifted (context constants n axisIndex q k time) j).gates=
 UniformCrossHeightPreparationMachine.gates
  (Header.forward (UniformLocalCacheSlotConductorMachine.Cursor.shifted
   (context constants n axisIndex q k time) j) q data.slot).chunk.height:=rfl

def snapshot (hq:0<q.e)(phase:Phase):UniformLayerSnapshot.Snapshot (Fin q.width):=
 UniformActualCalendarRectangleSnapshot.snapshot
  (UniformLocalCacheSlotConductorMachine.Cursor.shifted (context constants n axisIndex q k time) j)
  q data.slot data.layout data.broadcast
  ((forward_width _ q data.slot j).symm ▸ ha) ((forward_width _ q data.slot j).symm ▸ he)
  (rowBank q f) hq data.witness
  (gates constants n axisIndex q k time j ha he ambient f data) phase

def source (hq:0<q.e)
 (extent:q.offset+q.width≤(context constants n axisIndex q k time).ambient)
 (elapsed:ℕ):
 UniformActualCalendarLocalSources.Source
  (data.event _ _ _ _ _ _ _ _ elapsed)
  (snapshot constants n axisIndex q k time j ha he ambient f data hq (UniformActualCalendarRectangleProduced.phase elapsed))
  (UniformChunkPortMachine.intervalEmbedding (context constants n axisIndex q k time).ambient q.offset q.width extent):=
 UniformActualCalendarRectangleSnapshot.source
  (UniformLocalCacheSlotConductorMachine.Cursor.shifted (context constants n axisIndex q k time) j)
  q data.slot data.layout data.broadcast
  ((forward_width _ q data.slot j).symm ▸ ha) ((forward_width _ q data.slot j).symm ▸ he)
  (rowBank q f) hq data.witness
  (gates constants n axisIndex q k time j ha he ambient f data) extent elapsed
  (UniformActualCalendarRectangleProduced.phase elapsed)

/-- Native calendar membership determines the local tick; no output-matrix
premise is needed and the physical slot cursor remains shifted. -/
theorem snapshot_tick {hf:PowerSeries.constantCoeff f≠0}{L:List (Layer q.width)}
 (actual:Core f hf (.rectangle q) L)(p:Fin 28):
 (snapshot constants n axisIndex q k time j ha he ambient f data (positive actual)
  (phases.get ⟨p.val,by rw[phases_length];exact p.isLt⟩)).matrix=
 tick L (28*j+p.val):=by
 cases actual with
 | pair v o hv indices=>
  exact UniformActualCalendarShiftedSnapshot.snapshot_tick
   constants n axisIndex v o hv indices k time j data.slot
   ((forward_width _ _ data.slot j).symm ▸ ha)
   ((forward_width _ _ data.slot j).symm ▸ he) data.layout data.broadcast
   f data.witness p

end
end ExactFourierCircuits.UniformActualCalendarNativeRectangle

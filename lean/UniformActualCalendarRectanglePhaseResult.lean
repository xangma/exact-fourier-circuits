import UniformActualCalendarRectangleDataBank

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRectanglePhaseResult
noncomputable section
open OAI.ExactFourier UniformJointAllocation UniformAllAxisSeedPreparation
open UniformCanonicalCacheSlotGeometry UniformLocalRectangleDescriptors
open UniformActualCalendarRectangleProduced UniformActualCalendarRectangleDataBank
open UniformCalendarNativePieces UniformCalendarRenderTick UniformLocalFourierLayers

structure Result {r v:ℕ}(event:UniformGlobalCalendarDispatch.Event)(band:Fin v↪Fin r)
 (L:List (Layer v))(clock:ℕ) where
 snapshot:UniformLayerSnapshot.Snapshot (Fin v)
 source:UniformActualCalendarLocalSources.Source event snapshot band
 matrix:snapshot.matrix=tick L clock

variable (constants:Constants)(n:ℕ)(axisIndex:Fin (axisCount n))(q:Row)(k time j:ℕ)
 {B:ℕ}{s:UniformMachine.State}
 (ha:q.a≤UniformCrossHeightPreparationMachine.widthOf (context constants n axisIndex q k time).height)
 (he:q.e≤UniformCrossHeightPreparationMachine.widthOf (context constants n axisIndex q k time).height)
 (positive:2≤(context constants n axisIndex q k time).ambient)
 (data:Data (B:=B) (context constants n axisIndex q k time) q ha he
  (producerBank constants n axisIndex q k time) positive j s)

/-- A real producer Data record determines its explicit snapshot, ordered
source, and native local tick. No coefficient identity or matrix action is
supplied by the caller. -/
def phase_result
 {hf:PowerSeries.constantCoeff (NewtonFourier.invH (zeta (radix n axisIndex)))≠0}
 {L:List (Layer q.width)}
 (actual:Core (NewtonFourier.invH (zeta (radix n axisIndex))) hf (.rectangle q) L)
 (extent:q.offset+q.width≤radix n axisIndex)(elapsed:ℕ)(below:elapsed<28):
 Result (data.event _ _ _ _ _ _ _ _ elapsed)
  (UniformChunkPortMachine.intervalEmbedding (radix n axisIndex) q.offset q.width extent)
  L (28*j+elapsed):=by
 let d:=nativeData constants n axisIndex q k time j ha he positive data
 let S:=UniformActualCalendarNativeRectangle.snapshot constants n axisIndex q k time j ha he positive
  (NewtonFourier.invH (zeta (radix n axisIndex))) d
  (UniformActualCalendarNativeRectangle.positive actual) (phase elapsed)
 refine ⟨S,?_,?_⟩
 · have source:=UniformActualCalendarNativeRectangle.source constants n axisIndex q k time j ha he positive
    (NewtonFourier.invH (zeta (radix n axisIndex))) d
    (UniformActualCalendarNativeRectangle.positive actual) extent elapsed
   rw[nativeData_event] at source
   exact source
 · have result:=UniformActualCalendarNativeRectangle.snapshot_tick constants n axisIndex q k time j ha he positive
    (NewtonFourier.invH (zeta (radix n axisIndex))) d actual ⟨elapsed,below⟩
   simpa only[S,phase,Nat.mod_eq_of_lt below] using result

end
end ExactFourierCircuits.UniformActualCalendarRectanglePhaseResult

import UniformActualCalendarRectanglePhaseResult
import UniformCalendarNativeRenderFamily
import UniformCalendarPulledSourceAction

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarAtomSourceTransport
noncomputable section
open OAI.ExactFourier UniformLocalCacheTiming UniformGlobalCalendarUnion
open UniformCalendarNativePieces UniformLocalFourierLayers UniformActualCalendarRectanglePhaseResult
open UniformCalendarRenderTick

/-- A native cache phase is transported along the proved timed-descriptor
identity; call order is preserved and only interval coordinates are compared. -/
def native_result (r t:ℕ)(f:PowerSeries ℂ)(hf:PowerSeries.constantCoeff f≠0)
 (original pieceEvent:TimedEvent)(same:original=pieceEvent)
 (extent:UniformGlobalCalendarGeometry.Event.low pieceEvent.event+Event.width pieceEvent.event≤r)
 (band:Fin (Event.width original.event)↪Fin r)
 (coordinates:∀j,(band j).val=UniformGlobalCalendarGeometry.Event.low original.event+j.val)
 (event:UniformGlobalCalendarDispatch.Event)
 (produce:∀(L:List (Layer (Event.width pieceEvent.event))),Core f hf pieceEvent.event L→
  Result event (UniformChunkPortMachine.intervalEmbedding r
   (UniformGlobalCalendarGeometry.Event.low pieceEvent.event) (Event.width pieceEvent.event) extent) L (t-pieceEvent.start))
 (L:List (Layer (Event.width original.event)))(actual:Core f hf original.event L):
 Result event band L (t-original.start):=by
 subst original
 let result:=produce L actual
 have eq:UniformChunkPortMachine.intervalEmbedding r
  (UniformGlobalCalendarGeometry.Event.low pieceEvent.event) (Event.width pieceEvent.event) extent=band:=by
  ext j
  exact (coordinates j).symm
 exact ⟨result.snapshot,eq▸result.source,result.matrix⟩

structure Match {r v:ℕ}(event:UniformGlobalCalendarDispatch.Event)(band:Fin v↪Fin r)
 (target:UniformLayerSnapshot.Snapshot (Fin v)) where
 snapshot:UniformLayerSnapshot.Snapshot (Fin v)
 source:UniformActualCalendarLocalSources.Source event snapshot band
 matrix:snapshot.matrix=target.matrix

end
end ExactFourierCircuits.UniformCalendarAtomSourceTransport

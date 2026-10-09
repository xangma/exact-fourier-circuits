import UniformCalendarNativePieces

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarNativeRenderFamily
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformLocalCacheTiming UniformCalendarNativePieces
open UniformCalendarRenderPieces UniformCalendarRenderPlan UniformCalendarRenderActive
open UniformCalendarRenderSnapshot UniformGlobalCalendarUnion UniformCalendarRenderTick

lemma core_transport (f:PowerSeries ℂ)(hf:PowerSeries.constantCoeff f≠0)
 (e e':TimedEvent)(eq:e=e')(L:List (Layer (Event.width e'.event)))
 (actual:Core f hf e'.event L)(t:ℕ):
 ∃L':List (Layer (Event.width e.event)),Core f hf e.event L' ∧
  Matrix.reindex (finCongr (congrArg (fun q:TimedEvent=>Event.width q.event) eq).symm)
   (finCongr (congrArg (fun q:TimedEvent=>Event.width q.event) eq).symm)
   (tick L (t-e'.start))=tick L' (t-e.start):=by
 subst e'
 exact ⟨L,actual,rfl⟩

theorem localFamily_native {v:ℕ}(f:PowerSeries ℂ)(hf:PowerSeries.constantCoeff f≠0)
 (L:List (Piece v))(native:∀p∈L,Native f hf p)(t:ℕ)
 (i:ActiveIndex (L.map Piece.descriptor) t):
 ∃layers:List (Layer (Event.width ((L.map Piece.descriptor).get i.val).event)),
  Core f hf ((L.map Piece.descriptor).get i.val).event layers ∧
  (localFamily L t i).matrix=tick layers (t-((L.map Piece.descriptor).get i.val).start):=by
 obtain ⟨layers,actual,eq⟩:=core_transport f hf _ _ (pieceAt_descriptor L i.val)
  (pieceAt L i.val).layers (native _ (pieceAt_mem L i.val)) t
 refine ⟨layers,actual,?_⟩
 rw[localFamily,UniformLayerSnapshot.Snapshot.reindex_matrix,localSnapshot_matrix]
 exact eq

lemma transportFamily_native {v:ℕ}(f:PowerSeries ℂ)(hf:PowerSeries.constantCoeff f≠0)
 (L:List (Piece v))(E:List TimedEvent)(erase:L.map Piece.descriptor=E)
 (native:∀p∈L,Native f hf p)(t:ℕ)(i:ActiveIndex E t):
 ∃layers:List (Layer (Event.width (E.get i.val).event)),Core f hf (E.get i.val).event layers ∧
  (transportFamily L E erase t i).matrix=tick layers (t-(E.get i.val).start):=by
 subst E
 exact localFamily_native f hf L native t i

/-- The original render family's chosen snapshots expose only their matrix.
Their actual local layers nevertheless have the concrete native pair/direct
form needed to compare a separately generated explicit physical snapshot. -/
theorem renderFamily_native {v:ℕ}(P:UniformBalancedToeplitz.Plan v)(o start t:ℕ)
 (f:PowerSeries ℂ)(hf:PowerSeries.constantCoeff f≠0)
 (i:ActiveIndex (treeTimed start (UniformLocalCacheTreeMachine.ofPlan P o)) t):
 ∃layers:List (Layer (Event.width
  ((treeTimed start (UniformLocalCacheTreeMachine.ofPlan P o)).get i.val).event)),
  Core f hf ((treeTimed start (UniformLocalCacheTreeMachine.ofPlan P o)).get i.val).event layers ∧
  (renderFamily P o start t f hf i).matrix=
   tick layers (t-((treeTimed start (UniformLocalCacheTreeMachine.ofPlan P o)).get i.val).start):=
 transportFamily_native f hf (calendar P o start f hf) _ (descriptors P o start f hf)
  (calendar_native P o start f hf) t i

end
end ExactFourierCircuits.UniformCalendarNativeRenderFamily

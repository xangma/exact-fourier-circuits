import UniformActualCalendarShiftedSnapshot
import UniformCalendarExplicitPreparedRender

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarNativePieces
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformBalancedToeplitz UniformWorkspacePlanner
open UniformLocalCacheTiming UniformCalendarRenderPieces UniformCalendarRenderPlan
open UniformGlobalCalendarGeometry
open UniformGlobalCalendarUnion
open UniformCalendarRenderActive

/-- The local layers in the real recursive calendar are exactly one direct
word or one ragged pair render. Embedding and timestamps do not change them. -/
inductive Core (f:PowerSeries ℂ)(hf:PowerSeries.constantCoeff f≠0):
 (e:Event)→List (Layer (Event.width e))→Prop
 | direct (v o:ℕ)(cap:v<196):
   Core f hf (.direct v o) (UniformLocalFourierLayers.render (.direct v cap) f hf)
 | pair (v o:ℕ)(hv:0<selected v)
   (indices:Fin (chunkCount (v-v/2) (selected v))×Fin (chunkCount (v/2) (selected v))):
   Core f hf (.rectangle (UniformLocalRectangleDescriptors.row v o (selected v) indices.1.val indices.2.val))
    (pairSchedule v hv f indices)

def Native {v:ℕ}(f:PowerSeries ℂ)(hf:PowerSeries.constantCoeff f≠0)(p:Piece v):Prop:=
 Core f hf p.descriptor.event p.layers

lemma stamp_native {v:ℕ}(f:PowerSeries ℂ)(hf:PowerSeries.constantCoeff f≠0)
 (L:List (Piece v))(actual:∀p∈L,Native f hf p)(start:ℕ):
 ∀p∈stamp start L,Native f hf p:=by
 induction L generalizing start with
 | nil=>simp [stamp]
 | cons p L ih=>
  intro q member
  rcases List.mem_cons.mp member with rfl|member
  · exact actual p (by simp)
  · exact ih (fun q hq=>actual q (by simp [hq])) _ q member

lemma correction_native (v o start:ℕ)(hv:0<selected v)(f:PowerSeries ℂ)
 (hf:PowerSeries.constantCoeff f≠0):
 ∀p∈correctionPieces v hv o start f,Native f hf p:=by
 apply stamp_native
 intro p member
 obtain ⟨indices,_,rfl⟩:=List.mem_map.mp member
 exact Core.pair (f:=f) (hf:=hf) v o hv indices

theorem calendar_native {v:ℕ}(P:Plan v)(o start:ℕ)(f:PowerSeries ℂ)
 (hf:PowerSeries.constantCoeff f≠0):
 ∀p∈calendar P o start f hf,Native f hf p:=by
 induction P generalizing o start with
 | direct v cap=>
  intro p member
  have eq:p=(directPiece v cap o f hf).withStart start:=List.mem_singleton.mp member
  subst p
  exact Core.direct (f:=f) (hf:=hf) v o cap
 | split v hn hv L R ihL ihR=>
  intro p member
  rcases List.mem_append.mp member with member|member
  · rcases List.mem_append.mp member with member|member
    · obtain ⟨q,hq,rfl⟩:=List.mem_map.mp member
      exact ihL o start q hq
    · obtain ⟨q,hq,rfl⟩:=List.mem_map.mp member
      exact ihR (o+v/2) start q hq
  · exact correction_native v o _ hv f hf p member

theorem pieceAt_native {v:ℕ}(P:Plan v)(o start:ℕ)(f:PowerSeries ℂ)
 (hf:PowerSeries.constantCoeff f≠0)(i:Fin ((calendar P o start f hf).map Piece.descriptor).length):
 Native f hf (pieceAt (calendar P o start f hf) i):=
 calendar_native P o start f hf _ (pieceAt_mem _ i)

end
end ExactFourierCircuits.UniformCalendarNativePieces

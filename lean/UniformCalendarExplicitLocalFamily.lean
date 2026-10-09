import UniformCalendarPreparedRender

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarExplicitLocalFamily
noncomputable section
open OAI.ExactFourier UniformLayerSnapshot UniformGlobalCalendarUnion UniformLocalCacheTiming
open UniformCalendarRenderTick UniformCalendarRenderPieces UniformCalendarRenderActive
open UniformCalendarRenderSnapshot

/-- The actual local rendered tick, expressed in its timed event's coordinates. -/
def localPhaseMatrix {v : ℕ} (L : List (Piece v)) (t : ℕ)
    (i : ActiveIndex (L.map Piece.descriptor) t) :
    Matrix (Fin (Event.width ((L.map Piece.descriptor).get i.val).event))
      (Fin (Event.width ((L.map Piece.descriptor).get i.val).event)) ℂ :=
  Matrix.reindex
    (finCongr (congrArg (fun q : TimedEvent => Event.width q.event) (pieceAt_descriptor L i.val)).symm)
    (finCongr (congrArg (fun q : TimedEvent => Event.width q.event) (pieceAt_descriptor L i.val)).symm)
    (tick (pieceAt L i.val).layers (t-(pieceAt L i.val).descriptor.start))

lemma localFamily_matrix {v : ℕ} (L : List (Piece v)) (t : ℕ)
    (i : ActiveIndex (L.map Piece.descriptor) t) :
    (localFamily L t i).matrix = localPhaseMatrix L t i := by
  rw [localFamily, Snapshot.reindex_matrix, localSnapshot_matrix]
  rfl

/-- Transport explicit local phases through the genuine descriptor erasure. -/
def transport {v : ℕ} (L : List (Piece v)) (E : List TimedEvent)
    (erase : L.map Piece.descriptor=E) (t : ℕ) (S : Family (L.map Piece.descriptor) t) : Family E t :=
  Eq.mp (congrArg (fun E => Family E t) erase) S

lemma transport_agreement {v : ℕ} (L : List (Piece v)) (E : List TimedEvent)
    (erase : L.map Piece.descriptor=E) (t : ℕ) (S : Family (L.map Piece.descriptor) t)
    (phase : ∀ i,(S i).matrix=localPhaseMatrix L t i) :
    ∀ i,(transport L E erase t S i).matrix=(transportFamily L E erase t i).matrix := by
  subst E
  intro i
  exact (phase i).trans (localFamily_matrix L t i).symm

/-- Matrix agreement needs no assertion about an arbitrary chosen snapshot's
call indices or the orientation of its ordered endpoints. -/
lemma family_matrix {E : List TimedEvent} {t r : ℕ}
    (S T : Family E t)
    (e : (Σ i : ActiveIndex E t,Fin (Event.width (E.get i.val).event)) ↪ Fin r)
    (same : ∀ i,(S i).matrix=(T i).matrix) :
    ((UniformGlobalCalendarUnion.Snapshot.family S).embed e).matrix =
      ((UniformGlobalCalendarUnion.Snapshot.family T).embed e).matrix := by
  change ((UniformGlobalCalendarUnion.Snapshot.family (fun i => S i)).embed e).matrix =
    ((UniformGlobalCalendarUnion.Snapshot.family (fun i => T i)).embed e).matrix
  rw [Snapshot.embed_matrix, Snapshot.embed_matrix,
    UniformGlobalCalendarUnion.Snapshot.family_matrix, UniformGlobalCalendarUnion.Snapshot.family_matrix]
  congr 1
  apply congrArg Matrix.blockDiagonal'
  funext i
  exact same i

end
end ExactFourierCircuits.UniformCalendarExplicitLocalFamily

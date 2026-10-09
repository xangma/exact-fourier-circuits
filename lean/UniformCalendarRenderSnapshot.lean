import UniformCalendarRenderActive
import UniformCalendarRenderCorrespondence

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarRenderSnapshot
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformBalancedToeplitz UniformWorkspacePlanner
open UniformLocalCacheTiming UniformLocalCacheTreeMachine UniformLocalRectangleDescriptors
open UniformGlobalCalendarGeometry UniformGlobalCalendarUnion UniformLayerSnapshot
open UniformCalendarRenderTick UniformCalendarRenderPieces UniformCalendarRenderPlan
open UniformCalendarRenderPosition UniformCalendarRenderActive UniformCalendarRenderCorrespondence

def rootEmbedding (v o r : ℕ) (extent : o+v≤r) : Fin v ↪ Fin r where
  toFun i := ⟨o+i.val,by have:=i.isLt;omega⟩
  inj' := by intro i j h;apply Fin.ext;have:=congrArg Fin.val h;dsimp only at this;omega

def Family (E : List TimedEvent) (t : ℕ) : Type 1 :=
  ∀ i : ActiveIndex E t,Snapshot (Fin (Event.width (E.get i.val).event))

def transportFamily {v : ℕ} (L : List (Piece v)) (E : List TimedEvent)
    (erase : L.map Piece.descriptor=E) (t : ℕ) : Family E t :=
  Eq.mp (congrArg (fun E => Family E t) erase) (localFamily L t)

theorem transported_union_matrix {v : ℕ} (L : List (Piece v)) (E : List TimedEvent)
    (erase : L.map Piece.descriptor=E) (o t r : ℕ) (extent : o+v≤r)
    (e : (Σ i : ActiveIndex E t,Fin (Event.width (E.get i.val).event)) ↪ Fin r)
    (address : ∀ i j,(e ⟨i,j⟩).val = UniformGlobalCalendarGeometry.Event.low (E.get i.val).event+j.val)
    (position : ∀ p∈L,Positioned o p) :
    ((UniformGlobalCalendarUnion.Snapshot.family (transportFamily L E erase t)).embed e).matrix =
      Embedded.matrix (rootEmbedding v o r extent) (total L t) := by
  subst E
  apply union_total L t (rootEmbedding v o r extent) e
  intro i j
  apply Fin.ext
  rw [address]
  change UniformGlobalCalendarGeometry.Event.low ((L.map Piece.descriptor).get i.val).event+j.val =
    o+((pieceAt L i.val).position j).val
  rw [pieceAt_descriptor]
  exact (position _ (pieceAt_mem L i.val) j).symm

theorem transported_union {v : ℕ} (L : List (Piece v)) (E : List TimedEvent)
    (erase : L.map Piece.descriptor=E) (o t r : ℕ) (extent : o+v≤r)
    (e : (Σ i : ActiveIndex E t,Fin (Event.width (E.get i.val).event)) ↪ Fin r)
    (address : ∀ i j,(e ⟨i,j⟩).val = UniformGlobalCalendarGeometry.Event.low (E.get i.val).event+j.val)
    (position : ∀ p∈L,Positioned o p) :
    ∃ S : ∀ i : ActiveIndex E t,Snapshot (Fin (Event.width (E.get i.val).event)),
      ((UniformGlobalCalendarUnion.Snapshot.family S).embed e).matrix =
        Embedded.matrix (rootEmbedding v o r extent) (total L t) := by
  exact ⟨transportFamily L E erase t,
    transported_union_matrix L E erase o t r extent e address position⟩

def renderFamily {v : ℕ} (P : Plan v) (o start t : ℕ)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) :
    Family (treeTimed start (ofPlan P o)) t :=
  transportFamily (calendar P o start f hf) (treeTimed start (ofPlan P o))
    (descriptors P o start f hf) t

theorem treeSnapshot_renderFamily {v : ℕ} (P : Plan v) (o start t r : ℕ) (extent : o+v≤r)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) :
    (treeSnapshot P o start t r extent (renderFamily P o start t f hf)).matrix =
      if start≤t then Embedded.matrix (rootEmbedding v o r extent)
        (tick (UniformLocalFourierLayers.render P f hf) (t-start)) else 1 := by
  have eq:=transported_union_matrix (calendar P o start f hf) (treeTimed start (ofPlan P o))
    (descriptors P o start f hf) o t r extent (treeEmbedding P o start t r extent)
    (by intro i j;rfl) (calendar_positioned P o start f hf)
  change ((UniformGlobalCalendarUnion.Snapshot.family
    (transportFamily (calendar P o start f hf) (treeTimed start (ofPlan P o))
      (descriptors P o start f hf) t)).embed (treeEmbedding P o start t r extent)).matrix=_
  rw [eq,calendar_tick]
  by_cases on : start≤t
  · simp only [on,↓reduceIte]
  · simp only [on,↓reduceIte,Embedded.matrix_one]

/-- The real timed tree's active union equals the actual rendered tick.
Its local snapshots are constructed from the genuine local rendered layers.
No cache, execution, phase alignment or desired matrix is assumed. -/
theorem treeSnapshot_render {v : ℕ} (P : Plan v) (o start t r : ℕ) (extent : o+v≤r)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) :
    ∃ S : ∀ i : ActiveIndex (treeTimed start (ofPlan P o)) t,
      Snapshot (Fin (Event.width ((treeTimed start (ofPlan P o)).get i.val).event)),
      (treeSnapshot P o start t r extent S).matrix =
        if start≤t then Embedded.matrix (rootEmbedding v o r extent)
          (tick (UniformLocalFourierLayers.render P f hf) (t-start)) else 1 := by
  obtain ⟨S,eq⟩:=transported_union (calendar P o start f hf) (treeTimed start (ofPlan P o))
    (descriptors P o start f hf) o t r extent (treeEmbedding P o start t r extent)
    (by intro i j;rfl) (calendar_positioned P o start f hf)
  refine ⟨S,?_⟩
  change ((UniformGlobalCalendarUnion.Snapshot.family S).embed (treeEmbedding P o start t r extent)).matrix=_
  rw [eq]
  rw [calendar_tick]
  by_cases on : start≤t
  · simp only [on,↓reduceIte]
  · simp only [on,↓reduceIte,Embedded.matrix_one]

end
end ExactFourierCircuits.UniformCalendarRenderSnapshot

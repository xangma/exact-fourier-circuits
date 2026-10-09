import UniformCalendarRenderPosition
import UniformCalendarRenderUnion

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarRenderActive
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformLocalCacheTiming
open UniformGlobalCalendarGeometry UniformGlobalCalendarUnion UniformLayerSnapshot
open UniformCalendarRenderTick UniformCalendarRenderPieces UniformCalendarRenderPosition
open scoped BigOperators

def pieceAt {n : ℕ} (L : List (Piece n)) (i : Fin (L.map Piece.descriptor).length) : Piece n :=
  L.get ⟨i.val,by simpa only [List.length_map] using i.isLt⟩

theorem pieceAt_descriptor {n : ℕ} (L : List (Piece n)) (i : Fin (L.map Piece.descriptor).length) :
    (L.map Piece.descriptor).get i = (pieceAt L i).descriptor := by
  simp only [pieceAt,List.get_eq_getElem,List.getElem_map]

theorem pieceAt_mem {n : ℕ} (L : List (Piece n)) (i : Fin (L.map Piece.descriptor).length) :
    pieceAt L i ∈ L := List.get_mem _ _

theorem sum_pieceAt {n : ℕ} {α : Type} [AddCommMonoid α]
    (L : List (Piece n)) (f : Piece n → α) :
    ∑ i : Fin (L.map Piece.descriptor).length, f (pieceAt L i) = (L.map f).sum := by
  rw [←List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro j hj hk
    simp only [List.getElem_ofFn,List.getElem_map,pieceAt,List.get_eq_getElem]

theorem sum_active {n : ℕ} (L : List (Piece n)) (t : ℕ)
    {α : Type} [AddCommMonoid α] (f : Fin (L.map Piece.descriptor).length → α)
    (off : ∀ i,¬Active ((L.map Piece.descriptor).get i) t → f i=0) :
    ∑ i : ActiveIndex (L.map Piece.descriptor) t, f i.val = ∑ i, f i := by
  classical
  have eq:=Fintype.sum_subtype_add_sum_subtype
    (fun i => Active ((L.map Piece.descriptor).get i) t) f
  have zero : (∑ i : {i : Fin (L.map Piece.descriptor).length //
      ¬Active ((L.map Piece.descriptor).get i) t}, f i.val)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact off i.val i.property
  rw [zero,add_zero] at eq
  exact eq

def localSnapshot {n : ℕ} (p : Piece n) (t : ℕ) (on : Active p.descriptor t) :
    Snapshot (Fin (Event.width p.descriptor.event)) :=
  Classical.choose (layer_snapshot
    (p.layers.get ⟨t-p.descriptor.start,by
      rw [p.length]
      unfold Active TimedEvent.stop at on
      omega⟩)
    (p.restricted _ (List.get_mem _ _)))

theorem localSnapshot_matrix {n : ℕ} (p : Piece n) (t : ℕ) (on : Active p.descriptor t) :
    (localSnapshot p t on).matrix = tick p.layers (t-p.descriptor.start) := by
  rw [tick_of_lt p.layers _ (by rw [p.length];unfold Active TimedEvent.stop at on;omega)]
  exact (Classical.choose_spec (layer_snapshot _ (p.restricted _ (List.get_mem _ _)))).symm

/-- Each member is chosen from the actual restricted local rendered layer,
rather than supplied as a desired semantic result. -/
def localFamily {n : ℕ} (L : List (Piece n)) (t : ℕ)
    (i : ActiveIndex (L.map Piece.descriptor) t) :
    Snapshot (Fin (Event.width ((L.map Piece.descriptor).get i.val).event)) :=
  (localSnapshot (pieceAt L i.val) t (by rw [←pieceAt_descriptor];exact i.property)).reindex
    (finCongr (congrArg (fun q : TimedEvent => Event.width q.event) (pieceAt_descriptor L i.val)).symm)

theorem localFamily_embedded {n r : ℕ} (L : List (Piece n)) (t : ℕ)
    (root : Fin n ↪ Fin r)
    (e : (Σ i : ActiveIndex (L.map Piece.descriptor) t,
      Fin (Event.width ((L.map Piece.descriptor).get i.val).event)) ↪ Fin r)
    (compatible : ∀ (i : ActiveIndex (L.map Piece.descriptor) t)
      (j : Fin (Event.width (pieceAt L i.val).descriptor.event)),
      e ⟨i,Fin.cast (congrArg (fun q : TimedEvent => Event.width q.event)
        (pieceAt_descriptor L i.val)).symm j⟩ = root ((pieceAt L i.val).position j))
    (i : ActiveIndex (L.map Piece.descriptor) t) :
    Embedded.matrix ((Embedded.sigmaIn i).trans e) (localFamily L t i).matrix =
      Embedded.matrix root ((pieceAt L i.val).value t) := by
  rw [localFamily,Snapshot.reindex_matrix,←Embedded.matrix_equiv,Embedded.matrix_comp,
    localSnapshot_matrix]
  have eq : (finCongr (congrArg (fun q : TimedEvent => Event.width q.event)
      (pieceAt_descriptor L i.val)).symm).toEmbedding.trans ((Embedded.sigmaIn i).trans e) =
      (pieceAt L i.val).position.trans root := by
    ext j
    exact congrArg Fin.val (compatible i j)
  rw [eq,←Embedded.matrix_comp]
  have on : Active (pieceAt L i.val).descriptor t := by rw [←pieceAt_descriptor];exact i.property
  simp only [Piece.value,on,↓reduceIte]

theorem union_total {n r : ℕ} (L : List (Piece n)) (t : ℕ)
    (root : Fin n ↪ Fin r)
    (e : (Σ i : ActiveIndex (L.map Piece.descriptor) t,
      Fin (Event.width ((L.map Piece.descriptor).get i.val).event)) ↪ Fin r)
    (compatible : ∀ (i : ActiveIndex (L.map Piece.descriptor) t)
      (j : Fin (Event.width (pieceAt L i.val).descriptor.event)),
      e ⟨i,Fin.cast (congrArg (fun q : TimedEvent => Event.width q.event)
        (pieceAt_descriptor L i.val)).symm j⟩ = root ((pieceAt L i.val).position j)) :
    ((UniformGlobalCalendarUnion.Snapshot.family (localFamily L t)).embed e).matrix =
      Embedded.matrix root (total L t) := by
  rw [Snapshot.embed_matrix,UniformGlobalCalendarUnion.Snapshot.family_matrix,
    UniformCalendarRenderUnion.embedded_blocks_perturbations]
  simp only [localFamily_embedded L t root e compatible]
  rw [sum_active L t (fun i => Embedded.matrix root ((pieceAt L i).value t)-1) (by
    intro i off
    have inactive : ¬Active (pieceAt L i).descriptor t := by rw [pieceAt_descriptor] at off;exact off
    simp only [Piece.value,inactive,↓reduceIte,Embedded.matrix_one,sub_self])]
  rw [sum_pieceAt L (fun p => Embedded.matrix root (p.value t)-1)]
  exact (UniformCalendarRenderAffine.embed_sum_perturbations root L (fun p => p.value t)).symm

end
end ExactFourierCircuits.UniformCalendarRenderActive

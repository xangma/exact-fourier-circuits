import UniformTransposeCalendarGeometry

set_option autoImplicit false
namespace ExactFourierCircuits.UniformTransposeCalendarSnapshot
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformBalancedToeplitz UniformWorkspacePlanner
open UniformLocalCacheTiming UniformGlobalCalendarGeometry UniformGlobalCalendarUnion UniformLayerSnapshot
open UniformCalendarRenderPieces UniformCalendarRenderActive UniformCalendarRenderSnapshot

abbrev events {v : ℕ} (P : Plan v) (o start : ℕ) (f : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f≠0) :=
  (UniformTransposeCalendar.calendar P o start f hf).map Piece.descriptor

def embedding {v : ℕ} (P : Plan v) (o start t r : ℕ) (extent : o+v≤r)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    (Σ i : ActiveIndex (events P o start f hf) t,
      Fin (Event.width ((events P o start f hf).get i.val).event)) ↪ Fin r :=
  intervalEmbedding (σ := ActiveIndex (events P o start f hf) t) r
    (fun i => Event.low ((events P o start f hf).get i.val).event)
    (fun i => Event.width ((events P o start f hf).get i.val).event)
    (by
      intro i
      rw [←event_high]
      obtain ⟨p,hp,eq⟩:=List.mem_map.mp (List.get_mem (events P o start f hf) i.val)
      rw [←eq]
      have bound:=UniformTransposeCalendarGeometry.calendar_bounds P o start f hf p hp
      omega)
    (by
      intro i j ne
      have sep := active_separated (events P o start f hf) t
        (List.pairwise_map.mpr (UniformTransposeCalendarGeometry.calendar_separated P o start t f hf)) i j ne
      simpa only [DisjointBands,event_high] using sep)

def snapshot {v : ℕ} (P : Plan v) (o start t r : ℕ) (extent : o+v≤r)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) : Snapshot (Fin r) :=
  (UniformGlobalCalendarUnion.Snapshot.family
    (localFamily (UniformTransposeCalendar.calendar P o start f hf) t)).embed
      (embedding P o start t r extent f hf)

theorem snapshot_matrix {v : ℕ} (P : Plan v) (o start t r : ℕ) (extent : o+v≤r)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    (snapshot P o start t r extent f hf).matrix =
      if start≤t then Embedded.matrix (rootEmbedding v o r extent)
        (UniformCalendarRenderTick.tick (UniformTransposeTreeRender.render P f hf) (t-start)) else 1 := by
  have eq := transported_union_matrix
    (UniformTransposeCalendar.calendar P o start f hf) (events P o start f hf) rfl
    o t r extent (embedding P o start t r extent f hf)
    (by intro i j;rfl) (UniformTransposeCalendarGeometry.calendar_positioned P o start f hf)
  change (snapshot P o start t r extent f hf).matrix =
    Embedded.matrix (rootEmbedding v o r extent)
      (total (UniformTransposeCalendar.calendar P o start f hf) t) at eq
  rw [eq,UniformTransposeCalendar.calendar_tick]
  by_cases on : start≤t
  · simp only [on,↓reduceIte]
  · simp only [on,↓reduceIte,Embedded.matrix_one]

def axisSnapshot {r : ℕ} (P : Plan r) (f : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f≠0) (t : ℕ) : Snapshot (Fin r) :=
  snapshot P 0 0 t r (by omega) f hf

theorem axisSnapshot_matrix {r : ℕ} (P : Plan r) (f : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f≠0) (t : ℕ) :
    (axisSnapshot P f hf t).matrix =
      UniformCalendarRenderTick.tick (UniformTransposeTreeRender.render P f hf) t := by
  rw [axisSnapshot,snapshot_matrix]
  simp only [Nat.zero_le,↓reduceIte,Nat.sub_zero]
  have e : rootEmbedding r 0 r (by omega) = (Equiv.refl (Fin r)).toEmbedding := by
    ext i
    change 0+i.val=i.val
    omega
  rw [e,Embedded.matrix_equiv]
  rfl

end
end ExactFourierCircuits.UniformTransposeCalendarSnapshot

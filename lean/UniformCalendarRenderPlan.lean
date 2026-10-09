import UniformCalendarRenderPieces

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarRenderPlan
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformBalancedToeplitz UniformWorkspacePlanner
open UniformLocalCacheTiming UniformLocalCacheTreeMachine UniformLocalRectangleDescriptors
open UniformGlobalCalendarGeometry UniformGlobalCalendarUnion
open UniformCalendarRenderTick UniformCalendarRenderAffine UniformCalendarRenderPieces

def directPiece (v : ℕ) (cap : v < 196) (o : ℕ)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) : Piece v where
  descriptor := ⟨0,.direct v o⟩
  layers := UniformLocalFourierLayers.render (.direct v cap) f hf
  length := render_duration (.direct v cap) f hf
  position := Function.Embedding.refl _
  restricted := UniformLayerRestriction.render_restricted (.direct v cap) f hf

def pairPiece (v : ℕ) (hv : 0 < selected v) (o : ℕ) (f : PowerSeries ℂ)
    (q : Fin (chunkCount (v-v/2) (selected v)) × Fin (chunkCount (v/2) (selected v))) : Piece v where
  descriptor := ⟨0,.rectangle (row v o (selected v) q.1.val q.2.val)⟩
  layers := pairSchedule v hv f q
  length := pairSchedule_duration v hv f q
  position := Function.Embedding.refl _
  restricted := by
    unfold pairSchedule selectedSchedule chunkSchedule
    exact UniformLayerRestriction.shearLayers_restricted _ _
      (fun W hW => UniformToeplitzChunkWord.chunkLayers_matching _ _ _ _ _ _ W hW)

def correctionPieces (v : ℕ) (hv : 0 < selected v) (o start : ℕ) (f : PowerSeries ℂ) :
    List (Piece v) := stamp start ((pairs v).map (pairPiece v hv o f))

theorem correction_descriptors (v : ℕ) (hv : 0 < selected v) (o start : ℕ) (f : PowerSeries ℂ) :
    (correctionPieces v hv o start f).map Piece.descriptor =
      sequenceRows start (rows v o (selected v)) := by
  rw [rows_pairs]
  unfold correctionPieces
  generalize pairs v = L
  induction L generalizing start with
  | nil => rfl
  | cons q L ih =>
    simp only [List.map_cons,stamp,Piece.withStart,pairPiece,sequenceRows,ih,Event.duration]

/-- These are the actual local leaf and rectangle renders, including every
empty matching, stamped and embedded by the real plan's recursion. -/
def calendar {v : ℕ} (P : Plan v) (o start : ℕ)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) : List (Piece v) :=
  match P with
  | .direct v cap => [(directPiece v cap o f hf).withStart start]
  | .split v _ hv L R =>
    (calendar L o start f hf).map (fun p => p.embed (left v)) ++
    (calendar R (o+v/2) start f hf).map (fun p => p.embed (right v)) ++
    correctionPieces v hv o (start+max (planDuration L) (planDuration R)) f

theorem descriptors {v : ℕ} (P : Plan v) (o start : ℕ)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) :
    (calendar P o start f hf).map Piece.descriptor = treeTimed start (ofPlan P o) := by
  induction P generalizing o start with
  | direct v cap => rfl
  | split v hn hv L R ihL ihR =>
    simp only [calendar,List.map_append,List.map_map,Function.comp_def,Piece.embed,
      ihL,ihR,correction_descriptors,ofPlan,treeTimed,ofPlan_duration]

theorem calendar_inactive {v : ℕ} (P : Plan v) (o start t : ℕ)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0)
    (off : t < start ∨ start+planDuration P ≤ t) :
    total (calendar P o start f hf) t = 1 := by
  unfold total
  have h : ∀ p ∈ calendar P o start f hf, p.value t - 1 = 0 := by
    intro p hp
    have mem : p.descriptor ∈ treeTimed start (ofPlan P o) := by
      rw [←descriptors P o start f hf]
      exact List.mem_map.mpr ⟨p,hp,rfl⟩
    have b := timed_bounds (ofPlan P o) start p.descriptor mem
    rw [ofPlan_duration] at b
    have inactive : ¬Active p.descriptor t := by
      unfold Active
      rcases off with off | off <;> omega
    simp only [Piece.value,ite_eq_right inactive,sub_self]
  rw [List.sum_eq_zero (by intro a ha;obtain ⟨p,hp,rfl⟩:=List.mem_map.mp ha;exact h p hp)]
  exact add_zero _

end
end ExactFourierCircuits.UniformCalendarRenderPlan

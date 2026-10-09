import UniformCalendarRenderPlan

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarRenderCorrespondence
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformBalancedToeplitz UniformWorkspacePlanner
open UniformLocalCacheTiming UniformLocalCacheTreeMachine UniformLocalRectangleDescriptors
open UniformGlobalCalendarGeometry UniformGlobalCalendarUnion
open UniformCalendarRenderTick UniformCalendarRenderAffine UniformCalendarRenderPieces UniformCalendarRenderPlan

theorem embed_refl {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Embedded.matrix (Function.Embedding.refl _) M = M :=
  Embedded.matrix_equiv (Equiv.refl _) M

theorem correction_tick (v : ℕ) (hv : 0 < selected v) (o start t : ℕ) (f : PowerSeries ℂ) :
    total (correctionPieces v hv o start f) t =
      if start ≤ t then tick (correctionSchedule v hv f) (t-start) else 1 := by
  rw [correctionPieces,stamp_tick]
  have flat : ((pairs v).map (pairPiece v hv o f)).flatMap Piece.globalLayers =
      (correctionSchedule v hv f).map (Layer.embed (Function.Embedding.refl _)) := by
    simp only [Function.comp_def,Piece.globalLayers,pairPiece,
      correctionSchedule,List.map_flatten,List.map_map,List.flatMap_def,Event.width,row]
  rw [flat,tick_embed,embed_refl]

/-- Exact equality with the actual render at every global tick. The sum ranges
over every genuine event; inactive entries contribute zero perturbation. -/
theorem calendar_tick {v : ℕ} (P : Plan v) (o start t : ℕ)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) :
    total (calendar P o start f hf) t =
      if start ≤ t then tick (UniformLocalFourierLayers.render P f hf) (t-start) else 1 := by
  induction P generalizing o start with
  | direct v cap =>
    rw [calendar,total_cons,total_nil,Piece.at_withStart]
    simp only [Piece.globalLayers,directPiece,Event.width,tick_embed,embed_refl]
    abel
  | split v hn hv L R ihL ihR =>
    by_cases lo : start ≤ t
    · simp only [ite_eq_left lo]
      rw [calendar,total_append,total_append,total_embed,total_embed,correction_tick]
      change _ = tick (parallel (coordinates v) (UniformLocalFourierLayers.render L f hf)
        (UniformLocalFourierLayers.render R f hf) ++ correctionSchedule v hv f) (t-start)
      rw [tick_append,parallel_length,render_duration,render_duration]
      by_cases child : t-start < max (planDuration L) (planDuration R)
      · have before : ¬start+max (planDuration L) (planDuration R)≤t := by omega
        rw [ite_eq_left child,ite_eq_right before,ihL,ihR,ite_eq_left lo,ite_eq_left lo,
          tick_parallel,UniformCalendarRenderAffine.blocks_perturbations]
        change _ = Embedded.matrix (left v) _ + Embedded.matrix (right v) _ - 1
        abel
      · have after : start+max (planDuration L) (planDuration R)≤t := by omega
        rw [ite_eq_right child,ite_eq_left after,
          calendar_inactive L o start t f hf (Or.inr (by omega)),
          calendar_inactive R (o+v/2) start t f hf (Or.inr (by omega)),
          Embedded.matrix_one,Embedded.matrix_one]
        rw [show t-(start+max (planDuration L) (planDuration R))=
          t-start-max (planDuration L) (planDuration R) by omega]
        abel
    · rw [calendar_inactive (.split v hn hv L R) o start t f hf (Or.inl (by omega)),ite_eq_right lo]

end
end ExactFourierCircuits.UniformCalendarRenderCorrespondence

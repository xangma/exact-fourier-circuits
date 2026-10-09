import UniformTransposeTreeRender

set_option autoImplicit false
namespace ExactFourierCircuits.UniformTransposeCalendar
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformBalancedToeplitz UniformWorkspacePlanner
open UniformLocalCacheTiming UniformLocalRectangleDescriptors UniformGlobalCalendarUnion
open UniformCalendarRenderTick UniformCalendarRenderPieces UniformCalendarRenderCorrespondence
open UniformReverseParallelRender UniformCalendarRenderPosition

def directPiece (v : ℕ) (cap : v<196) (o : ℕ)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) : Piece v where
  descriptor := ⟨0,.direct v o⟩
  layers := UniformTransposeTreeRender.direct v f hf
  length := (UniformTransposeTreeRender.direct_length v cap f hf).trans
    (UniformLocalCacheTiming.render_duration (.direct v cap) f hf)
  position := Function.Embedding.refl _
  restricted := UniformTransposeTreeRender.direct_restricted v f hf

def pairPiece (v : ℕ) (hv : 0<selected v) (o : ℕ) (f : PowerSeries ℂ)
    (q : Fin (chunkCount (v-v/2) (selected v)) × Fin (chunkCount (v/2) (selected v))) : Piece v where
  descriptor := ⟨0,.rectangle (row v o (selected v) q.1.val q.2.val)⟩
  layers := UniformTransposeRectangleRender.upperPair v hv f q
  length := (UniformTransposeRectangleRender.upperPair_length v hv f q).trans
    (UniformLocalCacheTiming.pairSchedule_duration v hv f q)
  position := Function.Embedding.refl _
  restricted := UniformTransposeRectangleRender.upperPair_restricted v hv f q

def correctionPieces (v : ℕ) (hv : 0<selected v) (o start : ℕ) (f : PowerSeries ℂ) : List (Piece v) :=
  stamp start ((pairs v).reverse.map (pairPiece v hv o f))

theorem correction_tick (v : ℕ) (hv : 0<selected v) (o start t : ℕ) (f : PowerSeries ℂ) :
    total (correctionPieces v hv o start f) t =
      if start≤t then tick (UniformTransposeRectangleRender.correction v hv f) (t-start) else 1 := by
  rw [correctionPieces,stamp_tick]
  have flat : ((pairs v).reverse.map (pairPiece v hv o f)).flatMap Piece.globalLayers =
      (UniformTransposeRectangleRender.correction v hv f).map (Layer.embed (Function.Embedding.refl _)) := by
    simp only [Function.comp_def,Piece.globalLayers,pairPiece,
      UniformTransposeRectangleRender.correction,List.map_flatten,List.map_map,List.flatMap_def,Event.width,row]
  rw [flat,tick_embed,embed_refl]

def calendar {v : ℕ} (P : Plan v) (o start : ℕ)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) : List (Piece v) :=
  match P with
  | .direct v cap => [(directPiece v cap o f hf).withStart start]
  | .split v _ hv L R =>
    correctionPieces v hv o start f ++
    (calendar L o (start+(correctionSchedule v hv f).length+
      (max (planDuration L) (planDuration R)-planDuration L)) f hf).map (fun p => p.embed (left v)) ++
    (calendar R (o+v/2) (start+(correctionSchedule v hv f).length+
      (max (planDuration L) (planDuration R)-planDuration R)) f hf).map (fun p => p.embed (right v))


theorem shifted_tick {n : ℕ} (L : List (Layer n)) (start count delta t : ℕ)
    (ready : start+count≤t) :
    (if start+count+delta≤t then tick L (t-(start+count+delta)) else 1) =
      if delta≤t-start-count then tick L (t-start-count-delta) else 1 := by
  by_cases on : start+count+delta≤t
  · rw [ite_eq_left on,ite_eq_left (by omega)]
    congr 1
    omega
  · rw [ite_eq_right on,ite_eq_right (by omega)]

theorem calendar_tick {v : ℕ} (P : Plan v) (o start t : ℕ)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    total (calendar P o start f hf) t =
      if start≤t then tick (UniformTransposeTreeRender.render P f hf) (t-start) else 1 := by
  induction P generalizing o start with
  | direct v cap =>
    rw [calendar,total_cons,total_nil,Piece.at_withStart]
    simp only [Piece.globalLayers,directPiece,Event.width,tick_embed,embed_refl,
      UniformTransposeTreeRender.render]
    abel
  | split v hn hv L R ihL ihR =>
    rw [calendar,total_append,total_append,total_embed,total_embed,correction_tick,ihL,ihR]
    change _ = if start≤t then tick (UniformTransposeRectangleRender.correction v hv f ++
      frontParallel (coordinates v) (UniformTransposeTreeRender.render L f hf)
        (UniformTransposeTreeRender.render R f hf)) (t-start) else 1
    by_cases lo : start≤t
    · rw [ite_eq_left lo,tick_append,UniformTransposeRectangleRender.correction_length]
      by_cases before : t-start<(correctionSchedule v hv f).length
      · rw [ite_eq_left before,ite_eq_left lo,
          ite_eq_right (show ¬start+(correctionSchedule v hv f).length+
            (max (planDuration L) (planDuration R)-planDuration L)≤t by omega),
          ite_eq_right (show ¬start+(correctionSchedule v hv f).length+
            (max (planDuration L) (planDuration R)-planDuration R)≤t by omega),
          Embedded.matrix_one,Embedded.matrix_one]
        abel
      · rw [ite_eq_right before,ite_eq_left lo,
          tick_of_le (UniformTransposeRectangleRender.correction v hv f) (t-start)
            (by rw [UniformTransposeRectangleRender.correction_length];omega),
          frontParallel_tick,UniformTransposeTreeRender.render_length,
          UniformTransposeTreeRender.render_length,render_duration,render_duration,
          UniformCalendarRenderAffine.blocks_perturbations]
        change _ = Embedded.matrix (left v) _ + Embedded.matrix (right v) _ - 1
        rw [shifted_tick _ start _ _ t (by omega),shifted_tick _ start _ _ t (by omega)]
        abel
    · rw [ite_eq_right lo,ite_eq_right lo,
        ite_eq_right (show ¬start+(correctionSchedule v hv f).length+
          (max (planDuration L) (planDuration R)-planDuration L)≤t by omega),
        ite_eq_right (show ¬start+(correctionSchedule v hv f).length+
          (max (planDuration L) (planDuration R)-planDuration R)≤t by omega),
        Embedded.matrix_one,Embedded.matrix_one]
      abel

end
end ExactFourierCircuits.UniformTransposeCalendar

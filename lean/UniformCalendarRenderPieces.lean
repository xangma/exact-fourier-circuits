import UniformCalendarRenderAffine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarRenderPieces
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformLocalCacheTiming
open UniformGlobalCalendarGeometry UniformGlobalCalendarUnion
open UniformCalendarRenderTick UniformCalendarRenderAffine

/-- A genuine timed event together with its actual local rendered layers. -/
structure Piece (n : ℕ) where
  descriptor : TimedEvent
  layers : List (Layer (Event.width descriptor.event))
  length : layers.length = descriptor.event.duration
  position : Fin (Event.width descriptor.event) ↪ Fin n
  restricted : UniformLayerRestriction.ScheduleRestricted layers

namespace Piece
def embed {a n : ℕ} (p : Piece a) (e : Fin a ↪ Fin n) : Piece n :=
  { p with position := p.position.trans e }

def withStart {n : ℕ} (p : Piece n) (start : ℕ) : Piece n :=
  { p with descriptor := ⟨start,p.descriptor.event⟩ }

def globalLayers {n : ℕ} (p : Piece n) : List (Layer n) :=
  p.layers.map (Layer.embed p.position)

@[simp] theorem globalLayers_length {n : ℕ} (p : Piece n) :
    p.globalLayers.length = p.descriptor.event.duration := by
  simp only [globalLayers,List.length_map,p.length]

def value {n : ℕ} (p : Piece n) (t : ℕ) : Matrix (Fin n) (Fin n) ℂ := by
  classical
  exact if Active p.descriptor t then Embedded.matrix p.position (tick p.layers (t-p.descriptor.start)) else 1

theorem at_embed {a n : ℕ} (p : Piece a) (e : Fin a ↪ Fin n) (t : ℕ) :
    (p.embed e).value t = Embedded.matrix e (p.value t) := by
  by_cases h : Active p.descriptor t
  · simp [value,embed,h,← Embedded.matrix_comp]
  · simp [value,embed,h,Embedded.matrix_one]

theorem at_withStart {n : ℕ} (p : Piece n) (start t : ℕ) :
    (p.withStart start).value t =
      if start ≤ t then tick p.globalLayers (t-start) else 1 := by
  by_cases lo : start ≤ t
  · by_cases hi : t < start+p.descriptor.event.duration
    · simp [value,withStart,Active,TimedEvent.stop,lo,hi,globalLayers,tick_embed]
    · have endp : p.globalLayers.length ≤ t-start := by rw [globalLayers_length];omega
      simp only [value,withStart,Active,TimedEvent.stop]
      simp only [lo,hi,and_false,↓reduceIte]
      exact (tick_of_le _ _ endp).symm
  · simp [value,withStart,Active,TimedEvent.stop,lo]
end Piece

def total {n : ℕ} (L : List (Piece n)) (t : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + (L.map (fun p => p.value t - 1)).sum

@[simp] theorem total_nil (n t : ℕ) : total ([] : List (Piece n)) t = 1 := by simp [total]

theorem total_cons {n : ℕ} (p : Piece n) (L : List (Piece n)) (t : ℕ) :
    total (p::L) t = p.value t + total L t - 1 := by
  simp only [total,List.map_cons,List.sum_cons]
  abel

theorem total_append {n : ℕ} (L R : List (Piece n)) (t : ℕ) :
    total (L++R) t = total L t + total R t - 1 := by
  simp only [total,List.map_append,List.sum_append]
  abel

theorem total_embed {a n : ℕ} (L : List (Piece a)) (e : Fin a ↪ Fin n) (t : ℕ) :
    total (L.map (fun p => p.embed e)) t = Embedded.matrix e (total L t) := by
  simp only [total,List.map_map,Function.comp_def,Piece.at_embed]
  exact (embed_sum_perturbations e L (fun p => p.value t)).symm

/-- Successive local renders receive their actual sequential start times. -/
def stamp {n : ℕ} : ℕ → List (Piece n) → List (Piece n)
  | _,[] => []
  | start,p::L => p.withStart start :: stamp (start+p.descriptor.event.duration) L

theorem stamp_tick {n : ℕ} (L : List (Piece n)) (start t : ℕ) :
    total (stamp start L) t =
      if start ≤ t then tick (L.flatMap Piece.globalLayers) (t-start) else 1 := by
  induction L generalizing start with
  | nil => simp [stamp]
  | cons p L ih =>
    rw [stamp,total_cons,Piece.at_withStart,ih]
    simp only [List.flatMap_cons,tick_append,Piece.globalLayers_length]
    by_cases lo : start ≤ t
    · simp only [ite_eq_left lo]
      by_cases hi : t-start < p.descriptor.event.duration
      · have before : ¬start+p.descriptor.event.duration≤t := by omega
        simp only [ite_eq_left hi,ite_eq_right before]
        abel
      · have after : start+p.descriptor.event.duration≤t := by omega
        simp only [ite_eq_right hi,ite_eq_left after]
        rw [tick_of_le p.globalLayers (t-start) (by rw [Piece.globalLayers_length];omega)]
        rw [show t-(start+p.descriptor.event.duration)=t-start-p.descriptor.event.duration by omega]
        abel
    · have before : ¬start+p.descriptor.event.duration≤t := by omega
      simp only [ite_eq_right lo,ite_eq_right before]
      abel

end
end ExactFourierCircuits.UniformCalendarRenderPieces

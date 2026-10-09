import UniformAllAxisCalendarTensor

set_option autoImplicit false
namespace ExactFourierCircuits.UniformReverseParallelRender
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformCalendarRenderTick

def leading {n : ℕ} (count : ℕ) (L : List (Layer n)) :=
  List.replicate count (Layer.idle n) ++ L

@[simp] theorem leading_length {n : ℕ} (count : ℕ) (L : List (Layer n)) :
    (leading count L).length=count+L.length := by simp [leading]

@[simp] theorem leading_matrix {n : ℕ} (count : ℕ) (L : List (Layer n)) :
    matrix (leading count L)=matrix L := by
  simp [leading,matrix,List.map_replicate]

theorem leading_tick {n : ℕ} (count : ℕ) (L : List (Layer n)) (t : ℕ) :
    tick (leading count L) t = if count≤t then tick L (t-count) else 1 := by
  rw [leading,tick_append]
  by_cases h : count≤t
  · simp only [List.length_replicate,Nat.not_lt.mpr h,↓reduceIte,h]
  · have ht : t<count := by omega
    simp only [List.length_replicate,ht,↓reduceIte,h]
    have b : t<(List.replicate count (Layer.idle n)).length := by simpa using ht
    simp [tick,List.getElem?_eq_getElem b]

/-- Reverse-time padding is at the beginning of the shorter subtree. -/
def frontParallel {a b n : ℕ} (e : (Fin a ⊕ Fin b) ≃ Fin n)
    (L : List (Layer a)) (R : List (Layer b)) : List (Layer n) :=
  parallel e (leading (max L.length R.length-L.length) L)
    (leading (max L.length R.length-R.length) R)

@[simp] theorem frontParallel_length {a b n : ℕ} (e : (Fin a ⊕ Fin b) ≃ Fin n)
    (L : List (Layer a)) (R : List (Layer b)) :
    (frontParallel e L R).length=max L.length R.length := by
  rw [frontParallel,parallel_length,leading_length,leading_length]
  have l := Nat.le_max_left L.length R.length
  have r := Nat.le_max_right L.length R.length
  omega

theorem frontParallel_matrix {a b n : ℕ} (e : (Fin a ⊕ Fin b) ≃ Fin n)
    (L : List (Layer a)) (R : List (Layer b)) :
    matrix (frontParallel e L R) =
      Matrix.reindex e e (Matrix.fromBlocks (matrix L) 0 0 (matrix R)) := by
  rw [frontParallel,parallel_matrix,leading_matrix,leading_matrix]

theorem frontParallel_tick {a b n : ℕ} (e : (Fin a ⊕ Fin b) ≃ Fin n)
    (L : List (Layer a)) (R : List (Layer b)) (t : ℕ) :
    tick (frontParallel e L R) t = Matrix.reindex e e
      (Matrix.fromBlocks
        (if max L.length R.length-L.length≤t then tick L (t-(max L.length R.length-L.length)) else 1)
        0 0
        (if max L.length R.length-R.length≤t then tick R (t-(max L.length R.length-R.length)) else 1)) := by
  rw [frontParallel,tick_parallel,leading_tick,leading_tick]

end
end ExactFourierCircuits.UniformReverseParallelRender

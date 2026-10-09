import UniformTransposeRectangleRender
import UniformReverseParallelRender
import UniformDirectLeafTransposeLayers

set_option autoImplicit false
namespace ExactFourierCircuits.UniformTransposeTreeRender
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformBalancedToeplitz UniformWorkspacePlanner
open UniformReverseParallelRender UniformLayerRestriction

def direct (v : ℕ) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) : List (Layer v) :=
  if hv : 0<v then UniformDirectLeafTransposeLayers.transposeLeafLayers
    (fun i : Fin v => PowerSeries.coeff i.val f) hv
    (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hf) else []

theorem direct_matrix (v : ℕ) (cap : v<196) (f : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f≠0) :
    matrix (direct v f hf) = (matrix (UniformLocalFourierLayers.render (.direct v cap) f hf)).transpose := by
  unfold direct UniformLocalFourierLayers.render UniformBalancedToeplitz.render
  by_cases hv : 0<v
  · simp only [hv,↓reduceDIte]
    exact UniformDirectLeafTransposeLayers.transposeLeafLayers_matrix _ hv _
  · simp [hv,serial,matrix]

theorem direct_length (v : ℕ) (cap : v<196) (f : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f≠0) :
    (direct v f hf).length = (UniformLocalFourierLayers.render (.direct v cap) f hf).length := by
  unfold direct UniformLocalFourierLayers.render UniformBalancedToeplitz.render
  by_cases hv : 0<v
  · simp only [hv,↓reduceDIte,serial_length,
      UniformDirectLeafTransposeLayers.transposeLeafLayers_length,UniformDirectToeplitz.word_length]
  · simp [hv,serial]

theorem direct_restricted (v : ℕ) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
    ScheduleRestricted (direct v f hf) := by
  unfold direct
  split_ifs with hv
  · exact UniformDirectLeafTransposeLayers.transposeLeafLayers_restricted _ hv _
  · simp [ScheduleRestricted]

def render {v : ℕ} (P : Plan v) (f : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f≠0) : List (Layer v) :=
  match P with
  | .direct v _ => direct v f hf
  | .split v _ hv L R => UniformTransposeRectangleRender.correction v hv f ++
      frontParallel (coordinates v) (render L f hf) (render R f hf)

theorem render_matrix {v : ℕ} (P : Plan v) (f : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f≠0) :
    matrix (render P f hf) = (matrix (UniformLocalFourierLayers.render P f hf)).transpose := by
  induction P with
  | direct v cap => exact direct_matrix v cap f hf
  | split v hn hv L R ihL ihR =>
    simp only [render,UniformLocalFourierLayers.render,matrix_append,frontParallel_matrix,
      parallel_matrix,UniformTransposeRectangleRender.correction_matrix,ihL,ihR,
      Matrix.transpose_mul,Matrix.transpose_submatrix,Matrix.fromBlocks_transpose,
      Matrix.transpose_zero,Matrix.reindex_apply]

theorem render_length {v : ℕ} (P : Plan v) (f : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f≠0) :
    (render P f hf).length = (UniformLocalFourierLayers.render P f hf).length := by
  induction P with
  | direct v cap => exact direct_length v cap f hf
  | split v hn hv L R ihL ihR =>
    simp only [render,UniformLocalFourierLayers.render,List.length_append,frontParallel_length,
      parallel_length,UniformTransposeRectangleRender.correction_length,ihL,ihR]
    omega

theorem leading_restricted {v : ℕ} (k : ℕ) (L : List (Layer v)) (hL : ScheduleRestricted L) :
    ScheduleRestricted (leading k L) := by
  intro l hl
  rcases List.mem_append.mp hl with h|h
  · have eq := (List.mem_replicate.mp h).2
    subst l
    exact idle_restricted v
  · exact hL l h

theorem frontParallel_restricted {a b v : ℕ} (e : (Fin a ⊕ Fin b) ≃ Fin v)
    (L : List (Layer a)) (R : List (Layer b)) (hL : ScheduleRestricted L) (hR : ScheduleRestricted R) :
    ScheduleRestricted (frontParallel e L R) :=
  parallel_restricted _ _ _ (leading_restricted _ _ hL) (leading_restricted _ _ hR)

theorem render_restricted {v : ℕ} (P : Plan v) (f : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f≠0) : ScheduleRestricted (render P f hf) := by
  induction P with
  | direct v cap => exact direct_restricted v f hf
  | split v hn hv L R ihL ihR =>
    intro l hl
    rcases List.mem_append.mp hl with h|h
    · exact UniformTransposeRectangleRender.correction_restricted v hv f l h
    · exact frontParallel_restricted _ _ _ ihL ihR l h

end
end ExactFourierCircuits.UniformTransposeTreeRender

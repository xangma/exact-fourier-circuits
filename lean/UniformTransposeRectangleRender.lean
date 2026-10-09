import UniformTransposeMatchingRender
set_option autoImplicit false
namespace ExactFourierCircuits.UniformTransposeRectangleRender
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformToeplitzChunkWord UniformReplayPrint
open UniformWorkspacePlanner UniformDAGLayers UniformBalancedToeplitz
variable {v r e a : ℕ}

def upperChunk {H delta : ℕ} (D : UniformToeplitzCrossDAG.DAG r e a) (bank : Fin r → ℂ)
    (he : 0<e) (P : Placement e D.size a v) (hD : UniformToeplitzCrossDAG.DepthBound D H)
    (hd : 2≤delta) (huse : ∀ p,UniformToeplitzCrossDAG.physicalUseCount D p≤delta) : List (Layer v) :=
  UniformTransposeMatchingRender.layers bank (chunkLayers D he P hD hd huse) (chunkLayers_matching D he P hD hd huse)

theorem upperChunk_matrix {H delta : ℕ} (D : UniformToeplitzCrossDAG.DAG r e a) (bank : Fin r → ℂ)
    (he : 0<e) (P : Placement e D.size a v) (hD : UniformToeplitzCrossDAG.DepthBound D H)
    (hd : 2≤delta) (huse : ∀p,UniformToeplitzCrossDAG.physicalUseCount D p≤delta) :
    matrix (upperChunk D bank he P hD hd huse) =
      (matrix (chunkSchedule D bank he P hD hd huse)).transpose :=
  UniformTransposeMatchingRender.layers_matrix bank _ _

theorem upperChunk_length {H delta : ℕ} (D : UniformToeplitzCrossDAG.DAG r e a) (bank : Fin r → ℂ)
    (he : 0<e) (P : Placement e D.size a v) (hD : UniformToeplitzCrossDAG.DepthBound D H)
    (hd : 2≤delta) (huse : ∀p,UniformToeplitzCrossDAG.physicalUseCount D p≤delta) :
    (upperChunk D bank he P hD hd huse).length =
      (chunkSchedule D bank he P hD hd huse).length :=
  UniformTransposeMatchingRender.layers_length bank _ _

theorem upperChunk_restricted {H delta : ℕ} (D : UniformToeplitzCrossDAG.DAG r e a) (bank : Fin r → ℂ)
    (he : 0<e) (P : Placement e D.size a v) (hD : UniformToeplitzCrossDAG.DepthBound D H)
    (hd : 2≤delta) (huse : ∀p,UniformToeplitzCrossDAG.physicalUseCount D p≤delta) :
    UniformLayerRestriction.ScheduleRestricted (upperChunk D bank he P hD hd huse) :=
  UniformTransposeMatchingRender.layers_restricted bank _ _

def upperSelected (hv : 0<selected v)
    (ha : a∈chunkSizes (v-v/2) (selected v)) (he : e∈chunkSizes (v/2) (selected v))
    (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v) (hst : ∀ i j,source i≠target j)
    (bank : Fin (UniformToeplitzCrossDAG.bankSize (exponent a e)) → ℂ) : List (Layer v) :=
  upperChunk (printedCross a e) bank (chunk_pos hv he) (selectedPlacement hv ha he source target hst)
    (printedCross_depth a e) (by decide) (printedCross_fanout a e)

theorem upperSelected_matrix (hv : 0<selected v)
    (ha : a∈chunkSizes (v-v/2) (selected v)) (he : e∈chunkSizes (v/2) (selected v))
    (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v) (hst : ∀i j,source i≠target j)
    (bank : Fin (UniformToeplitzCrossDAG.bankSize (exponent a e)) → ℂ) :
    matrix (upperSelected hv ha he source target hst bank) = (matrix (selectedSchedule hv ha he source target hst bank)).transpose := upperChunk_matrix ..

theorem upperSelected_length (hv : 0<selected v)
    (ha : a∈chunkSizes (v-v/2) (selected v)) (he : e∈chunkSizes (v/2) (selected v))
    (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v) (hst : ∀i j,source i≠target j)
    (bank : Fin (UniformToeplitzCrossDAG.bankSize (exponent a e)) → ℂ) :
    (upperSelected hv ha he source target hst bank).length = (selectedSchedule hv ha he source target hst bank).length := upperChunk_length ..

theorem upperSelected_restricted (hv : 0<selected v)
    (ha : a∈chunkSizes (v-v/2) (selected v)) (he : e∈chunkSizes (v/2) (selected v))
    (source : Fin e ↪ Fin v) (target : Fin a ↪ Fin v) (hst : ∀i j,source i≠target j)
    (bank : Fin (UniformToeplitzCrossDAG.bankSize (exponent a e)) → ℂ) :
    UniformLayerRestriction.ScheduleRestricted (upperSelected hv ha he source target hst bank) := upperChunk_restricted _ _ _ _ _ _ _

def upperPair (n : ℕ) (hv : 0<selected n) (f : PowerSeries ℂ)
    (q : Fin (chunkCount (n-n/2) (selected n)) × Fin (chunkCount (n/2) (selected n))) : List (Layer n) :=
  let a := size (n-n/2) (selected n) q.1
  let e := size (n/2) (selected n) q.2
  let i₀ := n/2+q.1.val*selected n
  let j₀ := q.2.val*selected n
  let M := fun i j => ToeplitzLayers.cross (n/2) (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹) (i₀+i) (j₀+j)
  let v₀ := fun i => -PowerSeries.coeff (i₀+i-n/2) f
  let w₀ := fun j => PowerSeries.coeff (n/2-(j₀+j)) f⁻¹
  upperSelected hv (size_mem _ _ q.1) (size_mem _ _ q.2) (pairSource n hv q.2) (pairTarget n hv q.1)
    (fun _ _=>left_right n _ _) (UniformToeplitzCrossDAG.sharedBank (exponent a e)
      (UniformToeplitzCrossDAG.rankKernels (exponent a e) a e M v₀ w₀))


theorem upperPair_matrix (v : ℕ) (hv : 0<selected v) (f : PowerSeries ℂ)
    (q : Fin (chunkCount (v-v/2) (selected v)) × Fin (chunkCount (v/2) (selected v))) :
    matrix (upperPair v hv f q) = (matrix (pairSchedule v hv f q)).transpose :=
  by unfold upperPair pairSchedule;exact upperSelected_matrix ..

theorem upperPair_length (v : ℕ) (hv : 0<selected v) (f : PowerSeries ℂ)
    (q : Fin (chunkCount (v-v/2) (selected v)) × Fin (chunkCount (v/2) (selected v))) :
    (upperPair v hv f q).length = (pairSchedule v hv f q).length :=
  by unfold upperPair pairSchedule;exact upperSelected_length ..

theorem upperPair_restricted (v : ℕ) (hv : 0<selected v) (f : PowerSeries ℂ)
    (q : Fin (chunkCount (v-v/2) (selected v)) × Fin (chunkCount (v/2) (selected v))) :
    UniformLayerRestriction.ScheduleRestricted (upperPair v hv f q) :=
  by unfold upperPair;exact upperSelected_restricted _ _ _ _ _ _ _

/-- The actual rectangle macroorder reverses; standard swapped phases stay forward. -/
def correction (v : ℕ) (hv : 0<selected v) (f : PowerSeries ℂ) : List (Layer v) :=
  ((pairs v).reverse.map (upperPair v hv f)).flatten

theorem reverse_flatten_matrix {n : ℕ} {α : Type} (L : List α)
    (upper lower : α → List (Layer n))
    (h : ∀a∈L,matrix (upper a) = (matrix (lower a)).transpose) :
    matrix (L.reverse.map upper).flatten = (matrix (L.map lower).flatten).transpose := by
  induction L with
  | nil => simp [matrix]
  | cons a L ih =>
    simp only [List.reverse_cons,List.map_append,List.flatten_append,
      List.map_cons,List.flatten_cons,matrix_append,List.map_nil,List.flatten_nil,matrix_nil,one_mul]
    rw [h a (by simp),ih (fun a ha => h a (by simp [ha])),Matrix.transpose_mul]

theorem correction_matrix (v : ℕ) (hv : 0<selected v) (f : PowerSeries ℂ) :
    matrix (correction v hv f) = (matrix (correctionSchedule v hv f)).transpose :=
  reverse_flatten_matrix (pairs v) _ _ (fun _ _ => upperPair_matrix ..)

theorem correction_length (v : ℕ) (hv : 0<selected v) (f : PowerSeries ℂ) :
    (correction v hv f).length = (correctionSchedule v hv f).length := by
  simp only [correction,correctionSchedule,List.length_flatten,List.map_map,Function.comp_def,
    List.map_reverse,List.sum_reverse,upperPair_length]


theorem correction_restricted (v : ℕ) (hv : 0<selected v) (f : PowerSeries ℂ) :
    UniformLayerRestriction.ScheduleRestricted (correction v hv f) := by
  intro l hl
  obtain ⟨W,hW,mem⟩ := List.mem_flatten.mp hl
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hW
  exact upperPair_restricted v hv f q l mem

end
end ExactFourierCircuits.UniformTransposeRectangleRender

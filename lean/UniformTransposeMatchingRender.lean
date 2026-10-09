import UniformFourierCalendarEpoch
import UniformCalendarRenderMatching
import UniformCalendarRenderDirect

set_option autoImplicit false
namespace ExactFourierCircuits.UniformTransposeMatchingRender
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers UniformToeplitzChunkWord UniformReplayPrint
open UniformLayerRestriction UniformLayerSnapshot

def swap2 : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

theorem swapped_upper (mu : ℂ) :
    Matrix.reindex swap2 swap2 (upperShear mu) = (upperShear mu).transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap2,Matrix.reindex_apply,upperShear]

/-- Standard28 phases on swapped ordered endpoints. Internal phases are not reversed. -/
def swappedWord (mu : ℂ) : List (WordStep C 2) :=
  TensorWords.embeddedWord swap2.toEmbedding (UniformLocalShear.word mu)

theorem swappedWord_length (mu : ℂ) : (swappedWord mu).length=28 := by
  simp only [swappedWord,TensorWords.embeddedWord,List.length_map,localShear_length]

theorem swappedWord_matrix (mu : ℂ) :
    wordMatrix (swappedWord mu) = (upperShear mu).transpose := by
  rw [swappedWord,TensorWords.embeddedWord_matrix,UniformLocalShear.word_matrix,
    Embedded.matrix_equiv,swapped_upper]

theorem swappedWord_restricted (mu : ℂ) : WordRestricted (swappedWord mu) :=
  embeddedWord_restricted _ _ (localShear_restricted mu)

def matching {v r : ℕ} (bank : Fin r → ℂ) (W : List (ShearCode (Fin v) r)) (hm : Matching W) :
    List (Layer v) :=
  batchWords 28 (pairPosition W hm)
    (fun i => swappedWord ((W.get i).coefficient.eval bank)) (fun _ => swappedWord_length _)

@[simp] theorem matching_length {v r : ℕ} (bank : Fin r → ℂ)
    (W : List (ShearCode (Fin v) r)) (hm : Matching W) :
    (matching bank W hm).length=28 := batchWords_length ..

theorem matching_matrix {v r : ℕ} (bank : Fin r → ℂ)
    (W : List (ShearCode (Fin v) r)) (hm : Matching W) :
    matrix (matching bank W hm) = (matrix (matchingLayers bank W hm)).transpose := by
  rw [matching,batchWords_matrix,matchingLayers_matrix,matchingWord_matrix bank W hm,
    ←embedded_transpose,Matrix.blockDiagonal'_transpose]
  simp only [swappedWord_matrix]

theorem matching_restricted {v r : ℕ} (bank : Fin r → ℂ)
    (W : List (ShearCode (Fin v) r)) (hm : Matching W) :
    ScheduleRestricted (matching bank W hm) :=
  batchWords_restricted _ _ _ (fun _ => swappedWord_restricted _)

/-- Macroorder is reversed, while every actual swapped standard word retains
its chronological28-phase implementation. -/
def layers {v r : ℕ} (bank : Fin r → ℂ) (L : List (List (ShearCode (Fin v) r)))
    (hm : ∀W∈L,Matching W) : List (Layer v) :=
  (L.attach.reverse.map (fun W => matching bank W.val (hm W.val W.property))).flatten

theorem layers_length {v r : ℕ} (bank : Fin r → ℂ)
    (L : List (List (ShearCode (Fin v) r))) (hm : ∀W∈L,Matching W) :
    (layers bank L hm).length = (shearLayers bank L hm).length := by
  simp [layers,shearLayers,List.length_flatten,Function.comp_def]

theorem layers_matrix {v r : ℕ} (bank : Fin r → ℂ)
    (L : List (List (ShearCode (Fin v) r))) (hm : ∀W∈L,Matching W) :
    matrix (layers bank L hm) = (matrix (shearLayers bank L hm)).transpose := by
  induction L with
  | nil => simp [layers,shearLayers,matrix]
  | cons W L ih =>
    have upper : layers bank (W::L) hm =
        layers bank L (fun V hV => hm V (by simp [hV])) ++ matching bank W (hm W (by simp)) := by
      simp only [layers,List.attach_cons,List.reverse_cons,List.map_append,List.map_singleton,
        ←List.map_reverse,List.map_map,Function.comp_def,List.flatten_append,List.flatten_singleton]
    have lower : shearLayers bank (W::L) hm = matchingLayers bank W (hm W (by simp)) ++
        shearLayers bank L (fun V hV => hm V (by simp [hV])) := by
      simp only [shearLayers,List.attach_cons,List.map_cons,List.map_map,Function.comp_def,List.flatten_cons]
    rw [upper,lower,matrix_append,matrix_append,matching_matrix,ih,Matrix.transpose_mul]

theorem layers_restricted {v r : ℕ} (bank : Fin r → ℂ)
    (L : List (List (ShearCode (Fin v) r))) (hm : ∀W∈L,Matching W) :
    ScheduleRestricted (layers bank L hm) := by
  intro l hl
  obtain ⟨W,hW,mem⟩ := List.mem_flatten.mp hl
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hW
  exact matching_restricted bank q.val (hm q.val q.property) l mem


def swappedPosition {v r : ℕ} (W : List (ShearCode (Fin v) r)) (hm : Matching W) :
    (Σ _ : Fin W.length,Fin 2) ↪ Fin v :=
  (Equiv.sigmaCongrRight (fun _ : Fin W.length => swap2)).toEmbedding.trans (pairPosition W hm)

theorem swapped_blocks {s : ℕ} (M : Fin s → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.reindex (Equiv.sigmaCongrRight (fun _ : Fin s => swap2))
      (Equiv.sigmaCongrRight (fun _ : Fin s => swap2)) (Matrix.blockDiagonal' M) =
      Matrix.blockDiagonal' (fun i => Matrix.reindex swap2 swap2 (M i)) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  by_cases eq : i=j
  · subst j
    simp [Matrix.reindex_apply,Matrix.blockDiagonal'_apply]
  · simp [Matrix.reindex_apply,Matrix.blockDiagonal'_apply,eq]

/-- The physical transpose macro uses the same standard cached phase and the
same coefficient, on the swapped ordered pair. -/
theorem matching_phase {v r : ℕ} (bank : Fin r → ℂ)
    (W : List (ShearCode (Fin v) r)) (hm : Matching W) (p : Fin 28) :
    UniformCalendarRenderTick.tick (matching bank W hm) p.val =
      Embedded.matrix (swappedPosition W hm)
        (Matrix.blockDiagonal' (fun i => UniformGlobalCalendarPhases.phaseMatrix
          ((W.get i).coefficient.eval bank)
          (UniformGlobalMatchingScaleMachine.phases.get
            ⟨p.val,by rw [UniformGlobalMatchingScaleMachine.phases_length];exact p.isLt⟩))) := by
  rw [UniformCalendarRenderTick.tick_of_lt _ p.val (by rw [matching_length];exact p.isLt)]
  simp only [matching,batchWords,List.get_eq_getElem,List.getElem_ofFn,Layer.batch_matrix,
    Fin.cast,Fin.val_mk]
  simp only [swappedWord,TensorWords.embeddedWord,List.getElem_map,TensorWords.embedStep_matrix]
  rw [swappedPosition,←Embedded.matrix_comp,Embedded.matrix_equiv,swapped_blocks]
  congr 2
  funext i
  rw [Embedded.matrix_equiv]
  apply congrArg (Matrix.reindex swap2 swap2)
  simpa only [List.get_eq_getElem] using
    UniformGlobalCalendarPhases.word_phase_matrix ((W.get i).coefficient.eval bank) p


theorem layers_tick {v r : ℕ} (bank : Fin r → ℂ)
    (L : List (List (ShearCode (Fin v) r))) (hm : ∀W∈L,Matching W)
    (j : Fin L.attach.reverse.length) (p : Fin 28) :
    UniformCalendarRenderTick.tick (layers bank L hm) (28*j.val+p.val) =
      Embedded.matrix (swappedPosition (L.attach.reverse.get j).val
        (hm _ (L.attach.reverse.get j).property))
        (Matrix.blockDiagonal' (fun i => UniformGlobalCalendarPhases.phaseMatrix
          (((L.attach.reverse.get j).val.get i).coefficient.eval bank)
          (UniformGlobalMatchingScaleMachine.phases.get
            ⟨p.val,by rw [UniformGlobalMatchingScaleMachine.phases_length];exact p.isLt⟩))) := by
  have prefixLength : (((L.attach.reverse.take j.val).map
      (fun W => (matching bank W.val (hm W.val W.property)).length))).sum=28*j.val := by
    simp only [matching_length,List.map_const',List.sum_replicate,List.length_take,nsmul_eq_mul]
    rw [Nat.min_eq_left (Nat.le_of_lt j.isLt),Nat.mul_comm]
    simp only [Nat.cast_id]
  have tickEq:=UniformCalendarRenderDirect.flatten_tick L.attach.reverse
    (fun W => matching bank W.val (hm W.val W.property)) j p.val
    (by rw [matching_length];exact p.isLt)
  rw [prefixLength] at tickEq
  exact tickEq.trans (matching_phase bank _ _ p)

end
end ExactFourierCircuits.UniformTransposeMatchingRender

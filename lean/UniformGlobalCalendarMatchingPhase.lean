import UniformGlobalCalendarPhases
import UniformLayerSnapshotBlocks

set_option autoImplicit false

namespace ExactFourierCircuits.UniformGlobalCalendarMatchingPhase
noncomputable section
open OAI.ExactFourier UniformReplayPrint UniformToeplitzChunkWord UniformLocalFourierLayers
open UniformGlobalMatchingScaleMachine UniformGlobalMatchingScaleBankBridge UniformLayerRestriction
open UniformLayerSnapshot UniformGlobalCalendarPhases

/-- These are exactly the typed matching's ordered destination/source endpoints. -/
def edges {v R : ℕ} (W : List (ShearCode (Fin v) R)) : Fin W.length → UniformColoring.Edge :=
  fun i => ⟨(W.get i).dst.val,(W.get i).src.val,fun eq => (W.get i).different (Fin.ext eq)⟩

def coefficients {v R : ℕ} (bank : Fin R → ℂ) (W : List (ShearCode (Fin v) R)) : Fin W.length → ℂ :=
  fun i => (W.get i).coefficient.eval bank

lemma edges_matching {v R : ℕ} (W : List (ShearCode (Fin v) R)) (hm : Matching W) :
    UniformMatchingAxisTableMachine.Matching (edges W) := by
  intro i j ne
  have h := matching_get hm i j ne
  simp only [UniformColoring.Conflict,UniformColoring.Incident,edges]
  rintro ((eq|eq)|(eq|eq))
  · exact h.1 (Fin.ext eq.symm)
  · exact h.2.1 (Fin.ext eq.symm)
  · exact h.2.2.1 (Fin.ext eq.symm)
  · exact h.2.2.2 (Fin.ext eq.symm)

lemma factor_nonzero (mu : ℂ) (lane : Fin 9) (side : Fin 2) : factor mu lane side ≠ 0 := by
  fin_cases lane <;> fin_cases side <;>
    norm_num [factor,UniformLocalShear.kappa_ne_zero,UniformLocalShear.second_ne_zero,a_ne_zero]

lemma nativeFactor_nonzero {M : ℕ} (E : Fin M → UniformColoring.Edge) (mu : Fin M → ℂ)
    (lane : Fin 9) (i : ℕ) : nativeFactor E mu lane i ≠ 0 := by
  unfold nativeFactor
  split_ifs <;> first | exact factor_nonzero _ _ _ | exact one_ne_zero

lemma diagonal_blocks {s : ℕ} (d : Fin s → Fin 2 → ℂ) :
    Matrix.blockDiagonal' (fun i => Matrix.diagonal (d i)) =
      Matrix.diagonal (fun x : (Σ _ : Fin s, Fin 2) => d x.1 x.2) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  by_cases eq : i = j
  · subst j; simp [Matrix.blockDiagonal'_apply,Matrix.diagonal_apply]
  · simp [Matrix.blockDiagonal'_apply,eq]

/-- Every produced native factor, including unmatched-coordinate1, is the
same embedded diagonal used by the literal typed matching word. -/
theorem matching_diagonal {v R : ℕ} (bank : Fin R → ℂ)
    (W : List (ShearCode (Fin v) R)) (hm : Matching W) (lane : Fin 9) :
    Embedded.matrix (pairPosition W hm)
      (Matrix.blockDiagonal' (fun i => Matrix.diagonal (factor (coefficients bank W i) lane))) =
    Matrix.diagonal (fun i : Fin v => nativeFactor (edges W) (coefficients bank W) lane i.val) := by
  rw [diagonal_blocks,embedded_diagonal]
  congr 1
  funext i
  by_cases inside : i ∈ Set.range (pairPosition W hm)
  · obtain ⟨⟨j,side⟩,rfl⟩ := inside
    rw [Embedded.matrix_on,Matrix.diagonal_apply_eq]
    fin_cases side
    · exact (nativeFactor_left (edges W) (coefficients bank W) (edges_matching W hm) lane j).symm
    · exact (nativeFactor_right (edges W) (coefficients bank W) (edges_matching W hm) lane j).symm
  · rw [Embedded.matrix_off_row _ _ _ _ inside,ite_eq_left rfl]
    symm
    apply nativeFactor_unused
    intro j incident
    apply inside
    rcases incident with eq|eq
    · exact ⟨⟨j,0⟩,Fin.ext eq⟩
    · exact ⟨⟨j,1⟩,Fin.ext eq⟩

/-- Exact matrix of the real typed matching at an individual cached phase. -/
theorem matching_phase_matrix {v R : ℕ} (bank : Fin R → ℂ)
    (W : List (ShearCode (Fin v) R)) (hm : Matching W) (t : Fin 28) :
    ((matchingLayers bank W hm).get
      ⟨t.val,by rw [matchingLayers_length];exact t.isLt⟩).matrix =
    Embedded.matrix (pairPosition W hm)
      (Matrix.blockDiagonal' (fun i => phaseMatrix (coefficients bank W i)
        (phases.get ⟨t.val,by rw [phases_length];exact t.isLt⟩))) := by
  simp only [matchingLayers,batchWords,List.get_eq_getElem,List.getElem_ofFn,Layer.batch_matrix]
  congr 2
  funext i
  exact word_phase_matrix (coefficients bank W i) t

def matchingCalls {v R : ℕ} (W : List (ShearCode (Fin v) R)) (hm : Matching W) : Calls (Fin v) where
  index := Fin W.length
  finite := inferInstance
  dec := inferInstance
  position := pairPosition W hm

def phaseSnapshot {v R : ℕ} (bank : Fin R → ℂ) (W : List (ShearCode (Fin v) R))
    (hm : Matching W) : Phase → Snapshot (Fin v)
  | .diagonal lane => Snapshot.ofDiagonal
      (fun i => nativeFactor (edges W) (coefficients bank W) lane i.val)
      (fun i => nativeFactor_nonzero (edges W) (coefficients bank W) lane i.val)
  | .kernel => ⟨matchingCalls W hm,fun _ => 1,fun _ => one_ne_zero,fun _ => rfl⟩

/-- Each genuine typed matching phase supplies its own native snapshot, with
all ordered C endpoints and diagonal1 on every active call endpoint. -/
theorem matching_phase_snapshot {v R : ℕ} (bank : Fin R → ℂ)
    (W : List (ShearCode (Fin v) R)) (hm : Matching W) (t : Fin 28) :
    ((matchingLayers bank W hm).get
      ⟨t.val,by rw [matchingLayers_length];exact t.isLt⟩).matrix =
    (phaseSnapshot bank W hm (phases.get ⟨t.val,by rw [phases_length];exact t.isLt⟩)).matrix := by
  rw [matching_phase_matrix]
  generalize phases.get ⟨t.val,by rw [phases_length];exact t.isLt⟩ = phase
  cases phase with
  | diagonal lane =>
    rw [phaseSnapshot,Snapshot.ofDiagonal_matrix]
    exact matching_diagonal bank W hm lane
  | kernel =>
    simp only [phaseMatrix,phaseSnapshot,Snapshot.matrix,Matrix.diagonal_one,one_mul,Calls.matrix,matchingCalls]
    rfl

end
end ExactFourierCircuits.UniformGlobalCalendarMatchingPhase

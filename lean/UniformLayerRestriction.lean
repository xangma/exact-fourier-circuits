import UniformLocalFourierLayers

set_option autoImplicit false

namespace ExactFourierCircuits.UniformLayerRestriction
noncomputable section
open OAI.ExactFourier TypedKernelWords UniformLocalFourierLayers UniformReplayPrint

/-- Only diagonal monomial instructions and forward kernel calls. -/
def StepRestricted {n : ℕ} : WordStep C n → Prop
  | .monomial M _ => ∃ d, M = Matrix.diagonal d
  | .call _ => True

def Restricted {n : ℕ} : Layer n → Prop
  | .step s => StepRestricted s
  | .parallel _ L R => Restricted L ∧ Restricted R
  | .embed _ L => Restricted L
  | .batch _ steps => ∀ i, StepRestricted (steps i)

def WordRestricted {n : ℕ} (W : List (WordStep C n)) : Prop :=
  ∀ s ∈ W, StepRestricted s

def ScheduleRestricted {n : ℕ} (L : List (Layer n)) : Prop :=
  ∀ l ∈ L, Restricted l

theorem embedded_diagonal {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : β ↪ α) (d : β → ℂ) :
    Embedded.matrix e (Matrix.diagonal d) =
      Matrix.diagonal (fun i => Embedded.matrix e (Matrix.diagonal d) i i) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j; simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    by_cases hi : i ∈ Set.range e
    · obtain ⟨a, rfl⟩ := hi
      by_cases hj : j ∈ Set.range e
      · obtain ⟨b, rfl⟩ := hj
        rw [Embedded.matrix_on]
        exact Matrix.diagonal_apply_ne _ (fun h => hij (congrArg e h))
      · rw [Embedded.matrix_off_col e _ _ _ hj, ite_eq_right (by exact hij)]
    · rw [Embedded.matrix_off_row e _ _ _ hi, ite_eq_right (by exact hij)]

theorem embedStep_restricted {a n : ℕ} (e : Fin a ↪ Fin n)
    (s : WordStep C a) (hs : StepRestricted s) : StepRestricted (TensorWords.embedStep e s) := by
  cases s with
  | monomial M hM =>
    obtain ⟨d, rfl⟩ := hs
    exact ⟨_, embedded_diagonal e d⟩
  | call f => trivial

theorem embeddedWord_restricted {a n : ℕ} (e : Fin a ↪ Fin n)
    (W : List (WordStep C a)) (hW : WordRestricted W) :
    WordRestricted (TensorWords.embeddedWord e W) := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  exact embedStep_restricted e t (hW t ht)

@[simp] theorem diagonalStep_restricted (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    StepRestricted (diagonalStep x y hx hy) := by
  refine ⟨fun i => if i = 0 then x else y, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal]

@[simp] theorem forwardCall_restricted : StepRestricted forwardCall := trivial

theorem localShear_restricted (mu : ℂ) : WordRestricted (UniformLocalShear.word mu) := by
  simp [WordRestricted, UniformLocalShear.word, shearWord, hadamardWord]

theorem direct_shear_restricted {n : ℕ} (i : Fin n)
    (j : UniformDirectToeplitz.Source i) (mu : ℂ) :
    WordRestricted (UniformDirectToeplitz.shear i j mu) :=
  embeddedWord_restricted _ _ (localShear_restricted mu)

theorem direct_row_restricted {n : ℕ} (h : Fin n → ℂ) (hn : 0 < n)
    (h0 : h ⟨0, hn⟩ ≠ 0) (i : Fin n) :
    WordRestricted (UniformDirectToeplitz.row h hn h0 i) := by
  intro s hs
  simp only [UniformDirectToeplitz.row, List.mem_append, List.mem_singleton] at hs
  rcases hs with rfl | hs
  · exact ⟨_, rfl⟩
  · obtain ⟨W, hW, hs⟩ := List.mem_flatten.mp hs
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hW
    exact direct_shear_restricted i j _ s hs

theorem direct_partial_restricted {n : ℕ} (h : Fin n → ℂ) (hn : 0 < n)
    (h0 : h ⟨0, hn⟩ ≠ 0) (k : ℕ) (hk : k ≤ n) :
    WordRestricted (UniformDirectToeplitz.partialWord h hn h0 k hk) := by
  induction k with
  | zero => simp [UniformDirectToeplitz.partialWord, WordRestricted]
  | succ k ih =>
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact direct_row_restricted h hn h0 _ s hs
    · exact ih (by omega) s hs

theorem serial_restricted {n : ℕ} (W : List (WordStep C n)) (hW : WordRestricted W) :
    ScheduleRestricted (serial W) := by
  intro l hl
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hl
  exact hW s hs

@[simp] theorem idle_restricted (n : ℕ) : Restricted (Layer.idle n) :=
  ⟨fun _ => 1, Matrix.diagonal_one.symm⟩

theorem parallel_restricted {a b n : ℕ} (e : (Fin a ⊕ Fin b) ≃ Fin n)
    (L : List (Layer a)) (R : List (Layer b))
    (hL : ScheduleRestricted L) (hR : ScheduleRestricted R) :
    ScheduleRestricted (parallel e L R) := by
  induction L generalizing R with
  | nil =>
    induction R with
    | nil => simp [parallel, ScheduleRestricted]
    | cons r R ih =>
      intro l hl
      simp only [parallel] at hl
      rcases List.mem_cons.mp hl with rfl | hl
      · exact ⟨idle_restricted a, hR r (by simp)⟩
      · exact ih (fun x hx => hR x (by simp [hx])) l hl
  | cons l L ih =>
    cases R with
    | nil =>
      intro t ht
      simp only [parallel] at ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨hL l (by simp), idle_restricted b⟩
      · exact ih [] (fun x hx => hL x (by simp [hx])) hR t ht
    | cons r R =>
      intro t ht
      simp only [parallel] at ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨hL l (by simp), hR r (by simp)⟩
      · exact ih R (fun x hx => hL x (by simp [hx])) (fun x hx => hR x (by simp [hx])) t ht

theorem batchWords_restricted {s n T : ℕ} (position : (Σ _ : Fin s, Fin 2) ↪ Fin n)
    (W : Fin s → List (WordStep C 2)) (hW : ∀ i, (W i).length = T)
    (h : ∀ i, WordRestricted (W i)) : ScheduleRestricted (batchWords T position W hW) := by
  intro l hl
  obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hl
  intro i
  exact h i _ (List.get_mem _ _)

theorem matchingLayers_restricted {v r : ℕ} (bank : Fin r → ℂ)
    (W : List (ShearCode (Fin v) r)) (hW : UniformToeplitzChunkWord.Matching W) :
    ScheduleRestricted (matchingLayers bank W hW) :=
  batchWords_restricted _ _ _ (fun _ => localShear_restricted _)

theorem shearLayers_restricted {v r : ℕ} (bank : Fin r → ℂ)
    (L : List (List (ShearCode (Fin v) r)))
    (hL : ∀ W ∈ L, UniformToeplitzChunkWord.Matching W) :
    ScheduleRestricted (shearLayers bank L hL) := by
  intro l hl
  obtain ⟨W, hW, hl⟩ := List.mem_flatten.mp hl
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hW
  exact matchingLayers_restricted bank x.val _ l hl

theorem correctionSchedule_restricted (n : ℕ) (hv : 0 < UniformWorkspacePlanner.selected n)
    (f : PowerSeries ℂ) : ScheduleRestricted (correctionSchedule n hv f) := by
  intro l hl
  obtain ⟨W, hW, hl⟩ := List.mem_flatten.mp hl
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hW
  exact shearLayers_restricted _ _ (fun W hW => UniformToeplitzChunkWord.chunkLayers_matching _ _ _ _ _ _ W hW) l hl

theorem render_restricted {n : ℕ} (P : UniformBalancedToeplitz.Plan n)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) :
    ScheduleRestricted (render P f hf) := by
  induction P with
  | direct n cap =>
    unfold render UniformBalancedToeplitz.render
    split_ifs with hn
    · exact serial_restricted _ (direct_partial_restricted _ hn _ _ _)
    · simp [serial, ScheduleRestricted]
  | split n hn hv L R ihL ihR =>
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact parallel_restricted _ _ _ ihL ihR l hl
    · exact correctionSchedule_restricted n hv f l hl

end
end ExactFourierCircuits.UniformLayerRestriction

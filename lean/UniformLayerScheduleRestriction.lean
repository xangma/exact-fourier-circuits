import UniformLayerSnapshotBlocks
import UniformSynchronizedLayers

set_option autoImplicit false

namespace ExactFourierCircuits.UniformLayerRestriction
noncomputable section
open OAI.ExactFourier UniformLocalFourierLayers

theorem transposeStep_restricted {n : ℕ} (s : WordStep C n) (hs : StepRestricted s) :
    StepRestricted (UniformLocalFourierWord.transposeStep s) := by
  cases s with
  | monomial M hM =>
    obtain ⟨d,rfl⟩ := hs
    exact ⟨d, Matrix.diagonal_transpose d⟩
  | call e => trivial

theorem transposeLayer_restricted {n : ℕ} (L : Layer n) (hL : Restricted L) :
    Restricted L.transpose := by
  induction L with
  | step s => exact transposeStep_restricted s hL
  | parallel e L R ihL ihR => exact ⟨ihL hL.1, ihR hL.2⟩
  | embed e L ih => exact ih hL
  | batch position steps => exact fun i => transposeStep_restricted (steps i) (hL i)

theorem transpose_restricted {n : ℕ} (L : List (Layer n)) (hL : ScheduleRestricted L) :
    ScheduleRestricted (transpose L) := by
  intro l hl
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hl)
  exact transposeLayer_restricted x (hL x hx)

@[simp] theorem full_diagonalStep_restricted {n : ℕ} (d : Fin n → ℂ) (hd : ∀ i, d i ≠ 0) :
    Restricted (Layer.step (UniformLocalFourierWord.diagonalStep d hd)) := ⟨d, rfl⟩

theorem sandwich_restricted {n : ℕ} (left right : Fin n → ℂ)
    (hl : ∀ j, left j ≠ 0) (hr : ∀ j, right j ≠ 0)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) :
    ScheduleRestricted (sandwich left right hl hr f hf) := by
  intro l h
  simp only [sandwich, List.mem_append, List.mem_singleton] at h
  rcases h with (rfl | h) | rfl
  · exact full_diagonalStep_restricted right hr
  · exact render_restricted _ f hf l h
  · exact full_diagonalStep_restricted left hl

theorem symmetric_restricted {n : ℕ} (L : List (Layer n)) (hL : ScheduleRestricted L)
    (d : Fin n → ℂ) (hd : ∀ j, d j ≠ 0) : ScheduleRestricted (symmetric L d hd) := by
  intro l h
  simp only [symmetric, List.mem_append, List.mem_singleton] at h
  rcases h with (h | rfl) | h
  · exact transpose_restricted L hL l h
  · exact full_diagonalStep_restricted d hd
  · exact hL l h

theorem schedule_restricted {n : ℕ} (hn : 0 < n) {omega : ℂ}
    (hroot : IsPrimitiveRoot omega n) : ScheduleRestricted (schedule hn hroot) :=
  symmetric_restricted _ (sandwich_restricted _ _ _ _ _ _) _ _

theorem specifiedSchedule_restricted (n : ℕ) : ScheduleRestricted (specifiedSchedule n) := by
  unfold specifiedSchedule
  split_ifs with hn
  · exact schedule_restricted hn _
  · simp [ScheduleRestricted]

theorem preparedSchedule_restricted {n a : ℕ} (hn : 0 < n) {omega : ℂ}
    (hroot : IsPrimitiveRoot omega n) (s : UniformMachine.State)
    (hp : UniformNewtonTableMachine.PreparedOutputs n omega a s) :
    ScheduleRestricted (preparedSchedule hn hroot s hp) :=
  symmetric_restricted _ (sandwich_restricted _ _ _ _ _ _) _ _

theorem padded_restricted {n : ℕ} (T : ℕ) (L : List (Layer n)) (hL : ScheduleRestricted L) :
    ScheduleRestricted (UniformSynchronizedLayers.padded T L) := by
  intro l h
  rcases List.mem_append.mp h with h | h
  · exact hL l h
  · have he : l = Layer.idle n := (List.mem_replicate.mp h).2
    subst l
    exact idle_restricted n

theorem slot_restricted {n T : ℕ} (L : List (Layer n)) (h : L.length ≤ T)
    (hL : ScheduleRestricted L) (t : Fin T) :
    Restricted (UniformSynchronizedLayers.slot L h t) :=
  padded_restricted T L hL _ (List.get_mem _ _)

end
end ExactFourierCircuits.UniformLayerRestriction

namespace ExactFourierCircuits.UniformLayerSnapshot
noncomputable section
open OAI.ExactFourier UniformLayerRestriction UniformLocalFourierLayers UniformSynchronizedLayers

/-- Every actual synchronized local Fourier tick has one diagonal/C snapshot,
even when distinct parallel subtrees are in different compiler phases. -/
theorem synchronized_finite_snapshot (n : ℕ) (hn : 0 < n) (i : axes n)
    (t : Fin (UniformCommonSlots.slotCount n)) :
    ∃ (s : ℕ) (d : Fin (radix n i) → ℂ)
      (position : (Σ _ : Fin s, Fin 2) ↪ Fin (radix n i)),
      (∀ j, d j ≠ 0) ∧ (∀ j, d (position j) = 1) ∧
      (slot (localSchedules n i) (localSchedules_length hn i) t).matrix =
        Matrix.diagonal d * Embedded.matrix position (Matrix.blockDiagonal' (fun _ : Fin s => C)) :=
  finite_snapshot _ (slot_restricted _ _ (specifiedSchedule_restricted _) t)

end
end ExactFourierCircuits.UniformLayerSnapshot

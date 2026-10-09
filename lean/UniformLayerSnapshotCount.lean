import UniformLayerScheduleRestriction

set_option autoImplicit false

namespace ExactFourierCircuits.UniformLayerSnapshot
noncomputable section
open OAI.ExactFourier UniformLayerRestriction UniformLocalFourierLayers
open scoped BigOperators

theorem step_snapshot_count {n : ℕ} (s : WordStep C n) (hs : StepRestricted s) :
    ∃ S : Snapshot (Fin n), s.matrix = S.matrix ∧ Fintype.card S.calls.index = s.calls := by
  cases s with
  | monomial M hM =>
    obtain ⟨d,rfl⟩ := hs
    refine ⟨Snapshot.ofDiagonal d (monomial_diagonal_nonzero hM), ?_, ?_⟩
    · exact (Snapshot.ofDiagonal_matrix ..).symm
    · exact (Fintype.card_congr (Equiv.refl (Fin 0))).trans (by simp [WordStep.calls])
  | call e =>
    refine ⟨Snapshot.ofCall e, ?_, ?_⟩
    · rw [Snapshot.ofCall_matrix]; exact Packing.embeddedCall_eq _ _
    · exact (Fintype.card_congr (Equiv.refl (Fin 1))).trans (by simp [WordStep.calls])

theorem layer_snapshot_count {n : ℕ} (L : Layer n) (hL : Restricted L) :
    ∃ S : Snapshot (Fin n), L.matrix = S.matrix ∧ Fintype.card S.calls.index = L.calls := by
  induction L with
  | step s => simpa only [Layer.step_matrix, Layer.step_calls] using step_snapshot_count s hL
  | parallel e L R ihL ihR =>
    obtain ⟨S,hS,cS⟩ := ihL hL.1
    obtain ⟨T,hT,cT⟩ := ihR hL.2
    refine ⟨(S.sum T).reindex e, ?_, ?_⟩
    · rw [Layer.parallel_matrix, hS, hT, Snapshot.reindex_matrix, Snapshot.sum_matrix]
    · calc
        _ = Fintype.card (S.calls.index ⊕ T.calls.index) := Fintype.card_congr (Equiv.refl _)
        _ = L.calls + R.calls := by rw [Fintype.card_sum, cS, cT]
        _ = _ := (Layer.parallel_calls ..).symm
  | embed e L ih =>
    obtain ⟨S,hS,cS⟩ := ih hL
    refine ⟨S.embed e, ?_, ?_⟩
    · rw [Layer.embed_matrix, hS, Snapshot.embed_matrix]
    · exact (Fintype.card_congr (Equiv.refl S.calls.index)).trans
        (cS.trans (Layer.embed_calls ..).symm)
  | @batch s n position steps =>
    have h : ∀ i, ∃ S : Snapshot (Fin 2),
        (steps i).matrix = S.matrix ∧ Fintype.card S.calls.index = (steps i).calls :=
      fun i => step_snapshot_count (steps i) (hL i)
    choose S hS cS using h
    refine ⟨(Snapshot.blocks S).embed position, ?_, ?_⟩
    · rw [Layer.batch_matrix, Snapshot.embed_matrix, Snapshot.blocks_matrix]
      congr 2
      funext i
      exact hS i
    · calc
        _ = Fintype.card (Σ i, (S i).calls.index) := Fintype.card_congr (Equiv.refl _)
        _ = ∑ i, (steps i).calls := by simp only [Fintype.card_sigma, cS]
        _ = _ := (Layer.batch_calls ..).symm

/-- The normalized union retains every actual forward call, including zero-coefficient shears. -/
theorem finite_snapshot_count {n : ℕ} (L : Layer n) (hL : Restricted L) :
    ∃ (s : ℕ) (d : Fin n → ℂ) (position : (Σ _ : Fin s, Fin 2) ↪ Fin n),
      s = L.calls ∧ (∀ i, d i ≠ 0) ∧ (∀ i, d (position i) = 1) ∧
      L.matrix = Matrix.diagonal d *
        Embedded.matrix position (Matrix.blockDiagonal' (fun _ : Fin s => C)) := by
  obtain ⟨S,hS,cS⟩ := layer_snapshot_count L hL
  let e : (Σ _ : S.calls.index, Fin 2) ≃ (Σ _ : Fin (Fintype.card S.calls.index), Fin 2) :=
    Equiv.sigmaCongrLeft (β := fun _ : Fin (Fintype.card S.calls.index) => Fin 2)
      (Fintype.equivFin S.calls.index)
  let position := e.symm.toEmbedding.trans S.calls.position
  refine ⟨Fintype.card S.calls.index, S.diagonal, position, cS, S.nonzero, ?_, ?_⟩
  · intro i
    exact S.active_one (e.symm i)
  · rw [hS]
    change Matrix.diagonal S.diagonal * S.calls.matrix = _
    congr 1
    have h := Embedded.matrix_domain e S.calls.position
      (Matrix.blockDiagonal' (fun _ : S.calls.index => C))
    rw [constant_blocks_reindex] at h
    exact h.symm

theorem synchronized_finite_snapshot_count (n : ℕ) (hn : 0 < n)
    (i : UniformSynchronizedLayers.axes n) (t : Fin (UniformCommonSlots.slotCount n)) :
    let L := UniformSynchronizedLayers.slot (UniformSynchronizedLayers.localSchedules n i)
      (UniformSynchronizedLayers.localSchedules_length hn i) t
    ∃ (s : ℕ) (d : Fin (UniformSynchronizedLayers.radix n i) → ℂ)
      (position : (Σ _ : Fin s, Fin 2) ↪ Fin (UniformSynchronizedLayers.radix n i)),
      s = L.calls ∧ (∀ j, d j ≠ 0) ∧ (∀ j, d (position j) = 1) ∧
      L.matrix = Matrix.diagonal d *
        Embedded.matrix position (Matrix.blockDiagonal' (fun _ : Fin s => C)) :=
  finite_snapshot_count _ (slot_restricted _ _ (specifiedSchedule_restricted _) t)

end
end ExactFourierCircuits.UniformLayerSnapshot

import DFTModelOuterAlphaSource

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelOuterAlpha
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAdmissibilityControl
noncomputable section

theorem prepared_cell {s s0 : State} (same : StateMatch s s0) (q : ℕ) (y : ℂ)
    (present : s.scalarHeap q=some (UniformPairMachine.prepared y)) :
    s0.scalarHeap q=some (UniformPairMachine.prepared y) := by
  obtain ⟨b,hb,related⟩ := (same.scalarHeap q).left present
  have eq : UniformPairMachine.prepared y=b := related.eq_of_prepared rfl
  rw [←eq] at hb
  exact hb

theorem Entry.baseline {W V K S Q AP B : ℕ} {f : Fin V → Scalar}
    {roles : ℕ → Fin V → Scalar} {y : Fin V → ℂ} {alpha : Fin V ≃ Fin V} {s s0 : State}
    (entry : Entry W V K S Q AP B f roles y alpha s) (same : StateMatch s s0)
    (f0 : Fin V → Scalar) (roles0 : ℕ → Fin V → Scalar)
    (padded0 : ∀j : Fin V,s0.scalarHeap (K+j.val)=some (f0 j))
    (loaded0 : UniformRolePointwiseMachine.Source W V S roles0 s0) :
    Entry W V K S Q AP B f0 roles0 y alpha s0 where
  positiveRoles := entry.positiveRoles
  width := by simpa only [same.natReg] using entry.width
  paddedBase := by simpa only [same.natReg] using entry.paddedBase
  roleBase := by simpa only [same.natReg] using entry.roleBase
  savedBase := by simpa only [same.natReg] using entry.savedBase
  alphaBase := by simpa only [same.natReg] using entry.alphaBase
  padded := padded0
  loadedRoles := loaded0
  preparedSaved := fun j => prepared_cell same _ _ (entry.preparedSaved j)
  alphaTable := by simpa only [same.natHeap] using entry.alphaTable
  paddedSeparate := entry.paddedSeparate
  savedSeparate := entry.savedSeparate
  paddedFit := entry.paddedFit
  extent := entry.extent
  savedFit := entry.savedFit
  alphaFit := entry.alphaFit
  code := entry.code
  wordBound := same.wordBound entry.wordBound

/-- One typed gather encodes both actually executed padded-input permutations;
prepared saved-spectrum equality is derived only for its separate spectator. -/
theorem paired_execution {n W V K S Q AP B : ℕ} (x : Fin n → ℂ)
    (f f0 : Fin V → Scalar) (roles roles0 : ℕ → Fin V → Scalar)
    (y : Fin V → ℂ) (alpha : Fin V ≃ Fin V) (s s0 : State)
    (entry : Entry W V K S Q AP B f roles y alpha s) (same : StateMatch s s0)
    (padded0 : ∀j : Fin V,s0.scalarHeap (K+j.val)=some (f0 j))
    (loaded0 : UniformRolePointwiseMachine.Source W V S roles0 s0)
    (aT : Tape ℕ) (z roleTape : Tape Datum.T) (k : Tape ℂ)
    (alphaTape : ∀j : Fin V,aT.look j.val 0=(alpha j).val)
    (paddedTape : ∀j : Fin V,z.look j.val (0,(0,0))=DFTModelAffine.encodePaired (f j) (f0 j))
    (rolesTape : ∀r,r<W → ∀j : Fin V,roleTape.look (r*V+j.val) (0,(0,0))=
      DFTModelAffine.encodePaired (roles r j) (roles0 r j))
    (savedTape : ∀j : Fin V,k.look j.val 0=y j) :
    ∃u u0, UniformSequentialExecution.LocalStages n B x stages s (9*V+10) u ∧
      UniformSequentialExecution.LocalStages n B (fun _ => 0) stages s0 (9*V+10) u0 ∧
      Result W V K S Q f roles y alpha s u ∧ Result W V K S Q f0 roles0 y alpha s0 u0 ∧
      (∀j : Fin V,
        (run program (input V aT z roleTape k)).val.1.look j.val (0,(0,0))=
          DFTModelAffine.encodePaired (f (alpha j)) (f0 (alpha j)) ∧
        DFTModelAffine.Represents ((run program (input V aT z roleTape k)).val.1.look j.val (0,(0,0)))
          (f (alpha j))) ∧
      (∀j : Fin V,
        u.scalarHeap (Q+j.val)=some (UniformPairMachine.prepared
          ((run program (input V aT z roleTape k)).val.2.2.2.look j.val 0)) ∧
        u0.scalarHeap (Q+j.val)=some (UniformPairMachine.prepared
          ((run program (input V aT z roleTape k)).val.2.2.2.look j.val 0))) ∧
      (∀r,0<r → r<W → ∀j : Fin V,∃b b0,
        u.scalarHeap (S+r*V+j.val)=some b ∧ u0.scalarHeap (S+r*V+j.val)=some b0 ∧
        ScalarMatch b b0 ∧ (run program (input V aT z roleTape k)).val.2.2.1.look (r*V+j.val) (0,(0,0))=
          DFTModelAffine.encodePaired b b0) ∧
      (run program (input V aT z roleTape k)).valid ∧
      (run program (input V aT z roleTape k)).work≤3*(9*V+10) ∧
      (run program (input V aT z roleTape k)).peak≤B := by
  have baseline := entry.baseline same f0 roles0 padded0 loaded0
  have related : ∀j : Fin V,ScalarMatch (f j) (f0 j) := by
    intro j
    obtain ⟨b,hb,hm⟩ := (same.scalarHeap _).left (entry.padded j)
    have eq : b=f0 j := Option.some.inj (hb.symm.trans (padded0 j))
    simpa only [eq] using hm
  have relatedRoles : ∀r,r<W → ∀j : Fin V,ScalarMatch (roles r j) (roles0 r j) := by
    intro r hr j
    obtain ⟨b,hb,hm⟩ := (same.scalarHeap _).left (entry.loadedRoles r hr j)
    have eq : b=roles0 r j := Option.some.inj (hb.symm.trans (loaded0 r hr j))
    simpa only [eq] using hm
  obtain ⟨u,hu,result⟩ := execution x f roles y alpha s entry
  obtain ⟨u0,hu0,result0⟩ := execution (fun _ => 0) f0 roles0 y alpha s0 baseline
  refine ⟨u,u0,hu,hu0,result,result0,?_,?_,?_,program_valid _ _ _ _ _,work_preserved _ _ _ _ _,?_⟩
  · intro j
    have eq : (run program (input V aT z roleTape k)).val.1.look j.val (0,(0,0))=
        DFTModelAffine.encodePaired (f (alpha j)) (f0 (alpha j)) := by
      rw [program_value]
      exact (DFTModelOuterTailCRT.gather_lookup alpha aT z alphaTape j).trans (paddedTape (alpha j))
    exact ⟨eq,eq.symm ▸ DFTModelAffine.encodePaired_represents _ _ (related (alpha j))⟩
  · intro j
    rw [program_value]
    change u.scalarHeap (Q+j.val)=some (UniformPairMachine.prepared (k.look j.val 0)) ∧
      u0.scalarHeap (Q+j.val)=some (UniformPairMachine.prepared (k.look j.val 0))
    rw [savedTape j]
    exact ⟨result.preparedSaved j,result0.preparedSaved j⟩
  · intro r hr hrW j
    refine ⟨roles r j,roles0 r j,result.spectators r hr hrW j,result0.spectators r hr hrW j,
      relatedRoles r hrW j,?_⟩
    rw [program_value]
    exact rolesTape r hrW j
  · rw [program_peak]
    have h:=entry.width
    simpa only [h] using entry.wordBound.2.1 103

end
end ExactFourierCircuits.DFTModelOuterAlpha

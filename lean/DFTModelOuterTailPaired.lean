import DFTModelOuterTailSource

set_option autoImplicit false

/-! One typed execution encodes the actual and zero-input suffix runs.
Prepared coefficient equality is derived from StateMatch and genuine false
flags. Numerically equal tainted values are never treated as prepared. -/
namespace ExactFourierCircuits.DFTModelOuterTail
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAdmissibilityControl
noncomputable section

theorem paired_prepared_cell {s s0 : State} (same : StateMatch s s0)
    (q : ℕ) (y : ℂ) (present : s.scalarHeap q=some (UniformPairMachine.prepared y)) :
    s0.scalarHeap q=some (UniformPairMachine.prepared y) := by
  obtain ⟨b,hb,related⟩ := (same.scalarHeap q).left present
  have eq : UniformPairMachine.prepared y=b := related.eq_of_prepared rfl
  rw [←eq] at hb
  exact hb

theorem Entry.baseline {n V S T AP BI a c B : ℕ} {eta kappa : ℂ}
    {f : Fin V → Scalar} {alpha betaInverse : Fin V ≃ Fin V} {s s0 : State}
    (entry : Entry n V S T AP BI a c B eta kappa f alpha betaInverse s)
    (same : StateMatch s s0) (f0 : Fin V → Scalar)
    (source : ∀j : Fin V, s0.scalarHeap (S+j.val)=some (f0 j)) :
    Entry n V S T AP BI a c B eta kappa f0 alpha betaInverse s0 where
  positive := entry.positive
  count := by simpa only [same.natReg] using entry.count
  width := by simpa only [same.natReg] using entry.width
  sourceBase := by simpa only [same.natReg] using entry.sourceBase
  targetBase := by simpa only [same.natReg] using entry.targetBase
  alphaBase := by simpa only [same.natReg] using entry.alphaBase
  betaBase := by simpa only [same.natReg] using entry.betaBase
  chirpAddress := by simpa only [same.natReg] using entry.chirpAddress
  normalizationAddress := entry.normalizationAddress
  source := source
  alphaTable := by simpa only [same.natHeap] using entry.alphaTable
  betaTable := by simpa only [same.natHeap] using entry.betaTable
  coefficients := fun j hj => paired_prepared_cell same _ _ (entry.coefficients j hj)
  normalization := paired_prepared_cell same _ _ entry.normalization
  disjoint := entry.disjoint
  coefficientsBeforeSource := entry.coefficientsBeforeSource
  coefficientsBeforeTarget := entry.coefficientsBeforeTarget
  normalizationBeforeSource := entry.normalizationBeforeSource
  normalizationBeforeTarget := entry.normalizationBeforeTarget
  sourceFit := entry.sourceFit
  targetFit := entry.targetFit
  alphaFit := entry.alphaFit
  betaFit := entry.betaFit
  code := entry.code
  wordBound := same.wordBound entry.wordBound

theorem typed_output_lookup {n V : ℕ} (hV : 0<V) (eta kappa : ℂ)
    (f f0 : Fin V → Scalar) (alpha betaInverse : Fin V ≃ Fin V)
    (aT bT : Tape ℕ) (cT : Tape ℂ) (z : Tape Datum.T)
    (_alphaTape : ∀j : Fin V, aT.look j.val 0=(alpha j).val)
    (betaTape : ∀j : Fin V, bT.look j.val 0=(betaInverse j).val)
    (coefficientTape : ∀j,j<n → cT.look (2*j) 0=UniformChirp.chirp eta j)
    (dataTape : ∀j : Fin V, z.look j.val (0,(0,0))=DFTModelAffine.encodePaired (f j) (f0 j))
    (j : ℕ) (hj : j<n) :
    (run program (input n V aT bT cT kappa z)).val.2.look j (0,(0,0))=
      DFTModelAffine.encodePaired
        (UniformChirpOutputMachine.value hV eta kappa (fun q => f (betaInverse q)) j)
        (UniformChirpOutputMachine.value hV eta kappa (fun q => f0 (betaInverse q)) j) := by
  rw [program_value]
  change (Tape.tab n (fun q => DFTModelOuterTailOutput.value V q cT kappa
    (DFTModelOuterTailCRT.gatherValue V bT z))).look j (0,(0,0)) = _
  rw [Tape.look_of_lt _ _ hj]
  change DFTModelOuterTailOutput.value V j cT kappa
    (DFTModelOuterTailCRT.gatherValue V bT z) = _
  unfold DFTModelOuterTailOutput.value
  let q : Fin V := ⟨(V-j)%V,Nat.mod_lt _ hV⟩
  have gather : (DFTModelOuterTailCRT.gatherValue V bT z).look ((V-j)%V) (0,(0,0))=
      DFTModelAffine.encodePaired (f (betaInverse q)) (f0 (betaInverse q)) :=
    (DFTModelOuterTailCRT.gather_lookup betaInverse bT z betaTape q).trans (dataTape (betaInverse q))
  rw [gather,show j*2=2*j by omega,coefficientTape j hj]
  rw [DFTModelOuterTailOutput.scaled_paired _ _ _ kappa rfl,
    DFTModelOuterTailOutput.scaled_paired _ _ _ (UniformChirp.chirp eta j) rfl]
  rfl

theorem paired_execution {n V S T AP BI a c B : ℕ} (x : Fin n → ℂ) (eta kappa : ℂ)
    (f f0 : Fin V → Scalar) (alpha betaInverse : Fin V ≃ Fin V) (s s0 : State)
    (entry : Entry n V S T AP BI a c B eta kappa f alpha betaInverse s)
    (same : StateMatch s s0)
    (source0 : ∀j : Fin V, s0.scalarHeap (S+j.val)=some (f0 j))
    (aT bT : Tape ℕ) (cT : Tape ℂ) (z : Tape Datum.T)
    (alphaTape : ∀j : Fin V, aT.look j.val 0=(alpha j).val)
    (betaTape : ∀j : Fin V, bT.look j.val 0=(betaInverse j).val)
    (coefficientTape : ∀j,j<n → cT.look (2*j) 0=UniformChirp.chirp eta j)
    (dataTape : ∀j : Fin V, z.look j.val (0,(0,0))=DFTModelAffine.encodePaired (f j) (f0 j)) :
    ∃u u0, UniformSequentialExecution.LocalStages n B x stages s (18*V+13*n+36) u ∧
      UniformSequentialExecution.LocalStages n B (fun _ => 0) stages s0 (18*V+13*n+36) u0 ∧
      Result n V S T entry.positive eta kappa f alpha betaInverse u ∧
      Result n V S T entry.positive eta kappa f0 alpha betaInverse u0 ∧
      (∀j : Fin V,
        (run program (input n V aT bT cT kappa z)).val.1.1.look j.val (0,(0,0))=
          DFTModelAffine.encodePaired (f (betaInverse (alpha j))) (f0 (betaInverse (alpha j))) ∧
        (run program (input n V aT bT cT kappa z)).val.1.2.look j.val (0,(0,0))=
          DFTModelAffine.encodePaired (f (betaInverse j)) (f0 (betaInverse j))) ∧
      (∀j,j<n → ∃v v0,
        u.outputs j=some v.value ∧ u0.outputs j=some v0.value ∧ ScalarMatch v v0 ∧
        DFTModelAffine.Represents
          ((run program (input n V aT bT cT kappa z)).val.2.look j (0,(0,0))) v ∧
        (run program (input n V aT bT cT kappa z)).val.2.look j (0,(0,0))=
          DFTModelAffine.encodePaired v v0) ∧
      (run program (input n V aT bT cT kappa z)).valid ∧
      (run program (input n V aT bT cT kappa z)).work≤9*(18*V+13*n+36) ∧
      (run program (input n V aT bT cT kappa z)).peak≤B := by
  have baseline := entry.baseline same f0 source0
  have related : ∀j : Fin V, ScalarMatch (f j) (f0 j) := by
    intro j
    obtain ⟨v,present,h⟩ := (same.scalarHeap _).left (entry.source j)
    have eq : v=f0 j := Option.some.inj (present.symm.trans (source0 j))
    simpa only [eq] using h
  have scaledMatch (v v0 : Scalar) (k : ℂ) (h : ScalarMatch v v0) :
      ScalarMatch (UniformChirpOutputMachine.scaled k v) (UniformChirpOutputMachine.scaled k v0) :=
    ⟨h.flags,fun hv => congrArg (fun t : ℂ => k*t) (h.prepared hv)⟩
  obtain ⟨u,hu,result⟩ := execution x eta kappa f alpha betaInverse s entry
  obtain ⟨u0,hu0,result0⟩ := execution (fun _ => 0) eta kappa f0 alpha betaInverse s0 baseline
  refine ⟨u,u0,hu,hu0,result,result0,?_,?_,program_valid _ _ _ _ _ _ _,
    work_preserved _ _ _ _ _ _ _,(program_peak _ _ _ _ _ _ _).trans ?_⟩
  · intro j
    rw [program_value]
    exact ⟨(DFTModelOuterTailCRT.gather_lookup alpha aT _ alphaTape j).trans
      ((DFTModelOuterTailCRT.gather_lookup betaInverse bT z betaTape (alpha j)).trans (dataTape (betaInverse (alpha j)))),
      (DFTModelOuterTailCRT.gather_lookup betaInverse bT z betaTape j).trans (dataTape (betaInverse j))⟩
  · intro j hj
    let q : Fin V := ⟨(V-j)%V,Nat.mod_lt _ entry.positive⟩
    let v := UniformChirpOutputMachine.value entry.positive eta kappa (fun q => f (betaInverse q)) j
    let v0 := UniformChirpOutputMachine.value entry.positive eta kappa (fun q => f0 (betaInverse q)) j
    have hv : ScalarMatch v v0 := scaledMatch _ _ _
      (scaledMatch _ _ _ (related (betaInverse q)))
    have encoded := typed_output_lookup entry.positive eta kappa f f0 alpha betaInverse
      aT bT cT z alphaTape betaTape coefficientTape dataTape j hj
    exact ⟨v,v0,result.outputs j hj,result0.outputs j hj,hv,
      encoded.symm ▸ DFTModelAffine.encodePaired_represents v v0 hv,encoded⟩
  · have v : V≤B := by have h:=entry.sourceFit;omega
    have nn : 2*n≤B := by have h:=entry.coefficientsBeforeSource;have h':=entry.sourceFit;omega
    omega

end
end ExactFourierCircuits.DFTModelOuterTail

import DFTModelOuterMiddleSource

set_option autoImplicit false

/-! Both actual source runs are constructed. A single typed execution retains
the complete paired encoding at both gathered banks and all spectators.
Equality of the saved prepared spectrum follows from actual false flags. -/
namespace ExactFourierCircuits.DFTModelOuterMiddle
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

theorem Entry.baseline {W V S T Q AP BI B : ℕ} {v : ℕ → Fin V → Scalar} {y : Fin V → ℂ}
    {alpha betaInverse : Fin V ≃ Fin V} {s s0 : State}
    (entry : Entry W V S T Q AP BI B v y alpha betaInverse s) (same : StateMatch s s0)
    (v0 : ℕ → Fin V → Scalar) (source : UniformRolePointwiseMachine.Source W V S v0 s0) :
    Entry W V S T Q AP BI B v0 y alpha betaInverse s0 where
  roles := entry.roles
  width := by simpa only [same.natReg] using entry.width
  sourceBase := by simpa only [same.natReg] using entry.sourceBase
  targetBase := by simpa only [same.natReg] using entry.targetBase
  kernelBase := by simpa only [same.natReg] using entry.kernelBase
  alphaBase := by simpa only [same.natReg] using entry.alphaBase
  betaBase := by simpa only [same.natReg] using entry.betaBase
  source := source
  prepared := fun j => prepared_cell same _ _ (entry.prepared j)
  alphaTable := by simpa only [same.natHeap] using entry.alphaTable
  betaTable := by simpa only [same.natHeap] using entry.betaTable
  sourceTarget := entry.sourceTarget
  sourceKernel := entry.sourceKernel
  kernelTarget := entry.kernelTarget
  extent := entry.extent
  targetFit := entry.targetFit
  kernelFit := entry.kernelFit
  alphaFit := entry.alphaFit
  betaFit := entry.betaFit
  code := entry.code
  wordBound := same.wordBound entry.wordBound

theorem product_match {V : ℕ} (v v0 : ℕ → Fin V → Scalar) (y : Fin V → ℂ)
    (related : ∀j : Fin V, ScalarMatch (v 0 j) (v0 0 j)) (j : Fin V) :
    ScalarMatch (product v y j) (product v0 y j) :=
  ⟨(related j).flags,fun h => congrArg (fun z : ℂ => z*y j) ((related j).prepared h)⟩

theorem multiplied_paired {V : ℕ} (v v0 : ℕ → Fin V → Scalar) (y : Fin V → ℂ)
    (z : Tape Datum.T) (k : Tape ℂ)
    (dataTape : ∀j : Fin V, z.look j.val (0,(0,0))=DFTModelAffine.encodePaired (v 0 j) (v0 0 j))
    (kernelTape : ∀j : Fin V, k.look j.val 0=y j) (j : Fin V) :
    (multiplied V z k).look j.val (0,(0,0))=
      DFTModelAffine.encodePaired (product v y j) (product v0 y j) := by
  rw [multiplied_lookup,dataTape j,kernelTape j,scaled_paired]
  rfl

theorem paired_execution {n W V S T Q AP BI B : ℕ} (x : Fin n → ℂ)
    (v v0 : ℕ → Fin V → Scalar) (y : Fin V → ℂ) (alpha betaInverse : Fin V ≃ Fin V)
    (s s0 : State) (entry : Entry W V S T Q AP BI B v y alpha betaInverse s)
    (same : StateMatch s s0) (source0 : UniformRolePointwiseMachine.Source W V S v0 s0)
    (aT bT : Tape ℕ) (z : Tape Datum.T) (k : Tape ℂ)
    (alphaTape : ∀j : Fin V, aT.look j.val 0=(alpha j).val)
    (betaTape : ∀j : Fin V, bT.look j.val 0=(betaInverse j).val)
    (dataTape : ∀r,r<W → ∀j : Fin V, z.look (r*V+j.val) (0,(0,0))=
      DFTModelAffine.encodePaired (v r j) (v0 r j))
    (kernelTape : ∀j : Fin V, k.look j.val 0=y j) :
    ∃u u0, UniformSequentialExecution.LocalStages n B x stages s (27*V+27) u ∧
      UniformSequentialExecution.LocalStages n B (fun _ => 0) stages s0 (27*V+27) u0 ∧
      Result W V S T Q v y alpha betaInverse u ∧ Result W V S T Q v0 y alpha betaInverse u0 ∧
      (∀j : Fin V,
        (run program (input V aT bT z k)).val.1.1.look j.val (0,(0,0))=
          DFTModelAffine.encodePaired (product v y (betaInverse (alpha j)))
            (product v0 y (betaInverse (alpha j))) ∧
        (run program (input V aT bT z k)).val.1.2.look j.val (0,(0,0))=
          DFTModelAffine.encodePaired (product v y (betaInverse j)) (product v0 y (betaInverse j)) ∧
        DFTModelAffine.Represents ((run program (input V aT bT z k)).val.1.1.look j.val (0,(0,0)))
          (product v y (betaInverse (alpha j))) ∧
        DFTModelAffine.Represents ((run program (input V aT bT z k)).val.1.2.look j.val (0,(0,0)))
          (product v y (betaInverse j))) ∧
      (∀j : Fin V,
        u.scalarHeap (Q+j.val)=some (UniformPairMachine.prepared
          ((run program (input V aT bT z k)).val.2.1.look j.val 0)) ∧
        u0.scalarHeap (Q+j.val)=some (UniformPairMachine.prepared
          ((run program (input V aT bT z k)).val.2.1.look j.val 0))) ∧
      (∀r,0<r → r<W → ∀j : Fin V, ∃b b0,
        u.scalarHeap (S+r*V+j.val)=some b ∧ u0.scalarHeap (S+r*V+j.val)=some b0 ∧
        ScalarMatch b b0 ∧ (run program (input V aT bT z k)).val.2.2.look (r*V+j.val) (0,(0,0))=
          DFTModelAffine.encodePaired b b0) ∧
      (run program (input V aT bT z k)).valid ∧
      (run program (input V aT bT z k)).work≤4*(27*V+27) ∧
      (run program (input V aT bT z k)).peak≤B := by
  have baseline := entry.baseline same v0 source0
  have related : ∀r,r<W → ∀j : Fin V, ScalarMatch (v r j) (v0 r j) := by
    intro r hr j
    obtain ⟨a,present,h⟩ := (same.scalarHeap _).left (entry.source r hr j)
    have eq : a=v0 r j := Option.some.inj (present.symm.trans (source0 r hr j))
    simpa only [eq] using h
  have data0 : ∀j : Fin V, z.look j.val (0,(0,0))=DFTModelAffine.encodePaired (v 0 j) (v0 0 j) := by
    simpa only [Nat.zero_mul,Nat.zero_add] using dataTape 0 entry.roles
  have multiplyValues := multiplied_paired v v0 y z k data0 kernelTape
  obtain ⟨u,hu,result⟩ := execution x v y alpha betaInverse s entry
  obtain ⟨u0,hu0,result0⟩ := execution (fun _ => 0) v0 y alpha betaInverse s0 baseline
  refine ⟨u,u0,hu,hu0,result,result0,?_,?_,?_,program_valid _ _ _ _ _,
    work_preserved _ _ _ _ _,?_⟩
  · intro j
    have first : (run program (input V aT bT z k)).val.1.1.look j.val (0,(0,0))=
        DFTModelAffine.encodePaired (product v y (betaInverse (alpha j)))
          (product v0 y (betaInverse (alpha j))) := by
      rw [program_value]
      exact (DFTModelOuterTailCRT.gather_lookup alpha aT _ alphaTape j).trans
        ((DFTModelOuterTailCRT.gather_lookup betaInverse bT _ betaTape (alpha j)).trans
          (multiplyValues (betaInverse (alpha j))))
    have second : (run program (input V aT bT z k)).val.1.2.look j.val (0,(0,0))=
        DFTModelAffine.encodePaired (product v y (betaInverse j)) (product v0 y (betaInverse j)) := by
      rw [program_value]
      exact (DFTModelOuterTailCRT.gather_lookup betaInverse bT _ betaTape j).trans
        (multiplyValues (betaInverse j))
    exact ⟨first,second,first.symm ▸ DFTModelAffine.encodePaired_represents _ _
      (product_match v v0 y (related 0 entry.roles) _),
      second.symm ▸ DFTModelAffine.encodePaired_represents _ _
        (product_match v v0 y (related 0 entry.roles) _)⟩
  · intro j
    rw [program_value,kernelTape j]
    exact ⟨result.prepared j,result0.prepared j⟩
  · intro r hr hrW j
    refine ⟨v r j,v0 r j,result.spectators r hr hrW j,result0.spectators r hr hrW j,
      related r hrW j,?_⟩
    rw [program_value]
    exact dataTape r hrW j
  · rw [program_peak]
    have h:=entry.width
    simpa only [h] using entry.wordBound.2.1 103

end
end ExactFourierCircuits.DFTModelOuterMiddle

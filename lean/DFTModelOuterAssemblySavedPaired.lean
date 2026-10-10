import DFTModelOuterAssemblySavedSource

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelOuterAssemblySaved
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAdmissibilityControl
noncomputable section

/-- Equality of paired prepared banks follows from the source state relation
and the genuine prepared flag, including its equality-of-values clause. -/
theorem paired_prepared_cell {s s₀ : State} (same : StateMatch s s₀)
    (q : ℕ) (y : ℂ) (source : s.scalarHeap q=some (UniformPairMachine.prepared y)) :
    s₀.scalarHeap q=some (UniformPairMachine.prepared y) := by
  obtain ⟨b,present,related⟩ := (same.scalarHeap q).left source
  have eq : UniformPairMachine.prepared y=b := related.eq_of_prepared rfl
  rw [←eq] at present
  exact present

theorem Entry.baseline {W V S Q I K A B : ℕ} {v : Fin V → Scalar}
    {k y : Fin V → ℂ} {a : Fin V ≃ Fin V} {s s₀ : State}
    (entry : Entry W V S Q I K A B v k y a s) (same : StateMatch s s₀)
    (v₀ : Fin V → Scalar) (source : ∀j : Fin V, s₀.scalarHeap (I+j.val)=some (v₀ j)) :
    Entry W V S Q I K A B v₀ k y a s₀ where
  roles := entry.roles
  rolesFit := entry.rolesFit
  width := by simpa only [same.natReg] using entry.width
  base := by simpa only [same.natReg] using entry.base
  storage := by simpa only [same.natReg] using entry.storage
  alpha := by simpa only [same.natReg] using entry.alpha
  storageAddress := entry.storageAddress
  kernelAddress := by simpa only [same.natReg] using entry.kernelAddress
  inputAddress := entry.inputAddress
  inputSource := source
  kernelSource := fun j => paired_prepared_cell same _ _ (entry.kernelSource j)
  spectrumSource := fun j => paired_prepared_cell same _ _ (entry.spectrumSource j)
  alphaSource := by simpa only [same.natHeap] using entry.alphaSource
  inputBefore := entry.inputBefore
  kernelBefore := entry.kernelBefore
  separate := entry.separate
  extent := entry.extent
  tableFit := entry.tableFit
  code := entry.code
  low := by simpa only [same.natReg] using entry.low
  wordBound := same.wordBound entry.wordBound

theorem paired_execution {n W V S Q I K A B : ℕ} (x : Fin n → ℂ)
    (v v₀ : Fin V → Scalar) (k y : Fin V → ℂ) (a : Fin V ≃ Fin V)
    (s s₀ : State) (entry : Entry W V S Q I K A B v k y a s)
    (same : StateMatch s s₀)
    (zeroInput : ∀j : Fin V, s₀.scalarHeap (I+j.val)=some (v₀ j))
    (aT : Tape ℕ) (z : Tape DFTModelAffine.Tagged.T) (kT yT : Tape ℂ)
    (alphaSource : ∀j : Fin V, aT.look j.val 0=(a j).val)
    (dataSource : ∀j : Fin V, z.look j.val (0,(0,0))=DFTModelAffine.encodePaired (v j) (v₀ j))
    (kernelSource : ∀j : Fin V, kT.look j.val 0=k j)
    (spectrumSource : ∀j : Fin V, yT.look j.val 0=y j) :
    ∃u u₀,
      UniformSequentialExecution.LocalStages n B x (stages W) s
        ((7*V+9)+19+(5*(W*V)+16*V+24)) u ∧
      UniformSequentialExecution.LocalStages n B (fun _ => 0) (stages W) s₀
        ((7*V+9)+19+(5*(W*V)+16*V+24)) u₀ ∧
      Result W V S Q v k y a u ∧ Result W V S Q v₀ k y a u₀ ∧
      (∀j : Fin V,
        u.scalarHeap (Q+j.val)=some (UniformPairMachine.prepared
          ((run program ((V,yT),DFTModelOuterAssemblyRole.input W V aT z kT)).val.1.look j.val 0)) ∧
        u₀.scalarHeap (Q+j.val)=some (UniformPairMachine.prepared
          ((run program ((V,yT),DFTModelOuterAssemblyRole.input W V aT z kT)).val.1.look j.val 0))) ∧
      (∀i : Fin W, ∀j : Fin V, ∃b b₀,
        u.scalarHeap (S+i.val*V+j.val)=some b ∧ u₀.scalarHeap (S+i.val*V+j.val)=some b₀ ∧
        ScalarMatch b b₀ ∧
        (run program ((V,yT),DFTModelOuterAssemblyRole.input W V aT z kT)).val.2.look
          (i.val*V+j.val) (0,(0,0))=DFTModelAffine.encodePaired b b₀) ∧
      (run program ((V,yT),DFTModelOuterAssemblyRole.input W V aT z kT)).valid ∧
      (run program ((V,yT),DFTModelOuterAssemblyRole.input W V aT z kT)).work≤
        13*((7*V+9)+19+(5*(W*V)+16*V+24)) ∧
      (run program ((V,yT),DFTModelOuterAssemblyRole.input W V aT z kT)).peak≤B := by
  have baseline := entry.baseline same v₀ zeroInput
  have inputMatch : ∀j, ScalarMatch (v j) (v₀ j) := by
    intro j
    obtain ⟨b,present,related⟩ := (same.scalarHeap _).left (entry.inputSource j)
    have eq : b=v₀ j := Option.some.inj (present.symm.trans (zeroInput j))
    simpa only [eq] using related
  obtain ⟨u,hu,result⟩ := execution x v k y a s entry
  obtain ⟨u₀,hu₀,result₀⟩ := execution (fun _ => 0) v₀ k y a s₀ baseline
  refine ⟨u,u₀,hu,hu₀,result,result₀,?_,?_,program_valid _ _ _ _ _ _,
    work_preserved _ _ _ _ _ _,(program_peak _ _ _ _ _ _ entry.roles).trans ?_⟩
  · intro j
    rw [program_value,DFTModelMemoryCopy.program_value]
    have lookup : (Tape.tab V (fun q => yT.look q sc.blank)).look j.val 0=y j := by
      simpa only [Tape.look,Tape.tab,j.isLt,↓reduceDIte,Ty.blank] using spectrumSource j
    rw [lookup]
    exact ⟨result.saved j,result₀.saved j⟩
  · intro i j
    refine ⟨_,_,result.roles i j,result₀.roles i j,
      DFTModelOuterAssemblyRole.role_match v v₀ k a inputMatch i.val j,?_⟩
    rw [program_value]
    exact DFTModelOuterAssemblyRole.paired_lookup a v v₀ k aT z kT
      alphaSource dataSource kernelSource i j
  · have h := entry.extent
    omega

end
end ExactFourierCircuits.DFTModelOuterAssemblySaved

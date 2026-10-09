import DFTModelCRTMetadataSource

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCRTClosed
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformCRTTraversalCycle UniformSelectedPhysicalCRT UniformMachine
noncomputable section

attribute [local irreducible] program DFTModelCRT.program

theorem selected_work_source_budget {n : ℕ} (hn : 0<n) :
    (run program (DFTModelCRTMetadata.selectedInput n)).work≤
      9*(60*(len n+UniformAllAxisSeedPreparation.axisCount n+1)) := by
  have h := selected_work hn
  omega

/-- Genuine stage53 endpoint correspondence after computing the metadata inside
one typed program. The preceding source working-completion ABI is recorded in
MetadataSource.actual_source; neither a coefficient tape nor AP/BI is input. -/
theorem actual_stage (c : UniformJointAllocation.Constants) {n : ℕ} (hn : 0<n)
    (x : Fin n → ℂ) (s : State) (pc : s.pc=0)
    (args : UniformFastPhysicalCRTMachine.Args (UniformAllAxisSeedPreparation.axisCount n)
      (len n) (UniformFinalPhysicalTableGeometry.addresses c n) s)
    (core : UniformAxisCachePreparationRetention.Core n x s)
    (wb : WordBound (UniformJointAllocation.envelope c n) s) :
    ∃ticks u, BoundedExecution UniformFastPhysicalCRTMachine.program n x
        (UniformJointAllocation.envelope c n) s ticks u ∧
      ticks≤60*(len n+UniformAllAxisSeedPreparation.axisCount n+1) ∧ u.pc=52 ∧
      UniformFastPhysicalCRTMachine.Frame s u ∧
      (∀j : Fin (len n),
        u.natHeap ((UniformFinalPhysicalTableGeometry.addresses c n).physicalAlpha+j.val)=
          some ((run program (DFTModelCRTMetadata.selectedInput n)).val.1.look j.val 0) ∧
        u.natHeap ((UniformFinalPhysicalTableGeometry.addresses c n).inverseBeta+j.val)=
          some ((run program (DFTModelCRTMetadata.selectedInput n)).val.2.look j.val 0)) ∧
      (run program (DFTModelCRTMetadata.selectedInput n)).valid ∧
      (run program (DFTModelCRTMetadata.selectedInput n)).work≤520*(len n+1) ∧
      (run program (DFTModelCRTMetadata.selectedInput n)).peak≤(len n+1)^2 := by
  obtain ⟨ticks,u,execution,cost,up,_,_,frame,_,ap,bi⟩ :=
    UniformFinalPhysicalTableExecution.execution c hn x s pc args core wb
  refine ⟨ticks,u,execution,cost,up,frame,?_,selected_valid hn,selected_work hn,selected_peak hn⟩
  intro j
  rw [(selected_values hn j).1,(selected_values hn j).2]
  exact ⟨ap j,bi j⟩

end
end ExactFourierCircuits.DFTModelCRTClosed

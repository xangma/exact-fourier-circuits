import DFTModelCRTClosedProgram

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCRTMetadata
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformCRTTraversalCycle UniformSelectedPhysicalCRT UniformMachine
noncomputable section

/-- Read-only encoding of precisely the actual working-completion output ABI.
This semantic boundary supplies only a produced prime tape and three Nat headers. -/
def sourceInput (s : State) : Input.T :=
  (s.natReg 10,(s.natReg 17,(s.natReg 18,
    ⟨s.natReg 10,fun i => (s.natHeap i.val).getD 0⟩)))

theorem sourceInput_eq {n : ℕ} {s : State}
    (ready : UniformWorkingCompletion.PreparedState n s) : sourceInput s=selectedInput n := by
  rcases ready with ⟨⟨_,count,_,primes,_⟩,_,binary,volume⟩
  unfold sourceInput selectedInput
  rw [count,binary,volume]
  congr 4
  funext i
  rw [primes i.val i.isLt]
  rfl

/-- No coefficient table is assumed at the real source-state boundary. -/
theorem source_metadata {n : ℕ} (hn : 0<n) {s : State}
    (ready : UniformWorkingCompletion.PreparedState n s) :
    (run metadata (sourceInput s)).val=DFTModelCRT.selectedRows n := by
  rw [sourceInput_eq ready]
  exact selected_metadata hn

theorem source_tables {n : ℕ} (hn : 0<n) {s : State}
    (ready : UniformWorkingCompletion.PreparedState n s) :
    (run DFTModelCRTClosed.program (sourceInput s)).valid ∧
    (run DFTModelCRTClosed.program (sourceInput s)).work≤520*(len n+1) ∧
    (run DFTModelCRTClosed.program (sourceInput s)).peak≤(len n+1)^2 ∧
    (∀j : Fin (len n),
      (run DFTModelCRTClosed.program (sourceInput s)).val.1.look j.val 0=(physicalAlpha n j).val ∧
      (run DFTModelCRTClosed.program (sourceInput s)).val.2.look j.val 0=((physicalBeta n).symm j).val) := by
  rw [sourceInput_eq ready]
  exact ⟨DFTModelCRTClosed.selected_valid hn,DFTModelCRTClosed.selected_work hn,
    DFTModelCRTClosed.selected_peak hn,DFTModelCRTClosed.selected_values hn⟩

/-- The source boundary itself is reached by the proved real 46-cell preparation
from the empty initial state.  Translating that 46-cell stage into typed RAM is
separate; this theorem does not assume its output headers or prime tape. -/
theorem actual_source {n : ℕ} (hn : 0<n) (x : Fin n → ℂ) :
    ∃ticks s, BoundedExecution UniformWorkingCompletion.program n x ((n+2)^9) initial ticks s ∧
      s.pc=45 ∧ Represents n s (selectedInput n) ∧ sourceInput s=selectedInput n ∧
      ticks≤40000*(UniformWorkingLength.axisCount n+2)^4 ∧
      (run DFTModelCRTClosed.program (sourceInput s)).valid ∧
      (run DFTModelCRTClosed.program (sourceInput s)).work≤520*(len n+1) ∧
      (run DFTModelCRTClosed.program (sourceInput s)).peak≤(len n+1)^2 ∧
      (∀j : Fin (len n),
        (run DFTModelCRTClosed.program (sourceInput s)).val.1.look j.val 0=(physicalAlpha n j).val ∧
        (run DFTModelCRTClosed.program (sourceInput s)).val.2.look j.val 0=((physicalBeta n).symm j).val) := by
  obtain ⟨ticks,s,execution,ready,pc,_,_,_,_,_,cost⟩ :=
    UniformWorkingCompletion.preparation_execution hn x
  exact ⟨ticks,s,execution,pc,selected_represents ready,sourceInput_eq ready,cost,
    source_tables hn ready⟩

end
end ExactFourierCircuits.DFTModelCRTMetadata

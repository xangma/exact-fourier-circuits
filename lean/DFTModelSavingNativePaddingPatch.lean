import DFTModelSavingNativePaddingControl
import UniformRecursivePaddingRole

set_option autoImplicit false

/-! Paper E (adc7f), §2.6: the padding role patches only the two native
header cells, then runs the unchanged header reader before recursion. -/
namespace ExactFourierCircuits.DFTModelSavingNativePaddingPatch
open UniformMachine UniformRecursivePaddingFrames
open UniformFixedNetworkScheduleMachine (Record Printed)
noncomputable section

theorem execution (n B k q A F r stack depth U saved role last : ℕ)
    (record : Record) (x : Fin n→ℂ) (s : State)
    (pc : s.pc=P.address .paddingPatch)
    (parent : Parent k q A F r stack depth s)
    (metadata : Metadata F U saved role last s)
    (dest : s.natReg 4175=role) (printed : Printed U record.data s)
    (good : UniformFixedNetworkOpcodeMachine.WellFormed record)
    (unitEnd : U+record.data.length≤F-6) (low : 6≤F)
    (extent : U+record.data.length≤B) (width : record.width+1≤B)
    (bound : WordBound B s) (code : P.program.length≤B) :
    ∃u, BoundedRuns P.program n x B s (10+UniformFixedNetworkOpcodeMachine.headCost record) u ∧
      u.pc=P.address .residualInit ∧ Parent k q A F r stack depth u ∧
      Metadata F U saved role last u ∧
      UniformFixedNetworkOpcodeMachine.Fields U
        (UniformRecursivePaddingControl.patchRecord record q role) u ∧
      Printed U (UniformRecursivePaddingControl.patchRecord record q role).data u ∧
      u.natReg 2864=record.directions.length ∧ u.natReg 2865=U+record.data.length ∧
      UniformRecursivePaddingControl.Frame [U+1,U+3] s u := by
  obtain ⟨u,run,up,fields,bits,bank,body,finish,frame⟩:=
    UniformRecursivePaddingControl.patch_reader_execution n B F U q role k record x s pc
      parent.frontier parent.one low metadata.unit parent.columns dest parent.bits printed good
      bound extent width code
  have len:=Record.data_length record
  have metadataU : Metadata F U saved role last u := by
    apply metadata.transport
    intro z hz
    apply frame.natHeap
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hz ⊢
    rcases hz with rfl|rfl|rfl|rfl|rfl <;> omega
  exact ⟨u,run,up,parent.padding frame bits,metadataU,fields,bank,body,finish,frame⟩

end
end ExactFourierCircuits.DFTModelSavingNativePaddingPatch

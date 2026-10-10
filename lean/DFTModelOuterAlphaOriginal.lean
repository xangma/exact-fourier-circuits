import DFTModelOuterAlphaPaired
import UniformFinalOuterProgram

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelOuterAlpha
open UniformMachine UniformSequentialExecution UniformSequentialAssembly
noncomputable section

theorem original_stages (table : Program) :
    stages=((UniformFinalOuterProgram.stagesFor table).drop 12).take 1 := rfl

/-- The original false-mode header identifies the padded-input source7312,
separately from saved prepared-spectrum7300. -/
theorem original_padded_header (c : UniformJointAllocation.Constants) (n W : ℕ) (s : State)
    (metadata : UniformPermutationInversePreparation.Metadata n s)
    (source : s.natReg 6026=2*UniformJointAllocation.slab c n)
    (physical : s.natReg 7310=UniformKernelSpectrumStorage.alphaBase c n) :
    (UniformNatBlockMachine.applyBlock (UniformFinalOuterHeaders.roleArgs W false) s).natReg 7312=
      UniformPaddedInputPreparation.dataBase n :=
  (UniformFinalOuterHeaders.roleArgs_values c n W false s metadata source physical).padded

theorem original_saved_header (c : UniformJointAllocation.Constants) (n W : ℕ) (s : State)
    (metadata : UniformPermutationInversePreparation.Metadata n s)
    (source : s.natReg 6026=2*UniformJointAllocation.slab c n)
    (physical : s.natReg 7310=UniformKernelSpectrumStorage.alphaBase c n) :
    (UniformNatBlockMachine.applyBlock (UniformFinalOuterHeaders.roleArgs W false) s).natReg 7300=
      UniformKernelSpectrumStorage.base c n :=
  (UniformFinalOuterHeaders.roleArgs_values c n W false s metadata source physical).storage

theorem stages_size : size stages=18 := by
  simp only [stages,size,UniformPhysicalCRTConsumerMachine.alphaProgram_length]

def nativeProgram : Program := UniformSequentialAssembly.program stages

theorem nativeProgram_length : nativeProgram.length=19 := by
  rw [nativeProgram,UniformSequentialAssembly.program_length,stages_size]

/-- Terminated assembly includes its sole final halt in addition to the
helper's charged continuation halt: exactly 9V+11 ticks. -/
theorem assembled_execution {n W V K S Q AP B : ℕ} (x : Fin n → ℂ) (f : Fin V → Scalar)
    (roles : ℕ → Fin V → Scalar) (y : Fin V → ℂ) (alpha : Fin V ≃ Fin V) (s : State)
    (entry : Entry W V K S Q AP B f roles y alpha s) :
    ∃u,Result W V K S Q f roles y alpha s u ∧
      BoundedExecution nativeProgram n x B {s with pc:=0} (9*V+11) {u with pc:=18} := by
  obtain ⟨u,joined,result⟩ := execution x f roles y alpha s entry
  have fit : size stages≤B := by rw [stages_size];exact entry.code
  have assembled := joined.execution fit
  refine ⟨u,result,?_⟩
  simpa only [nativeProgram,stages_size,Nat.add_assoc] using assembled

end
end ExactFourierCircuits.DFTModelOuterAlpha

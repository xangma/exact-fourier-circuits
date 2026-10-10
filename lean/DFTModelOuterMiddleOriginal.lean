import DFTModelOuterMiddlePaired
import UniformFinalOuterProgram

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelOuterMiddle
open UniformMachine UniformSequentialExecution UniformSequentialAssembly
noncomputable section

/-- Exact original stages 15–16, with stage 14's clock result still the genuine
entry obligation. No clock traversal is asserted by this bounded join. -/
theorem original_stages (table : Program) :
    stages=((UniformFinalOuterProgram.stagesFor table).drop 14).take 2 := rfl

theorem stages_size : size stages=51 := by
  simp only [stages,size,UniformRolePointwiseMachine.program_length,
    UniformPhysicalCRTConsumerMachine.program_length]

def nativeProgram : Program := UniformSequentialAssembly.program stages

theorem nativeProgram_length : nativeProgram.length=52 := by
  rw [nativeProgram,UniformSequentialAssembly.program_length,stages_size]

/-- The assembled suffix includes its sole final halt in addition to the two
local helpers' charged continuation halts: 27V+28 actual native ticks. -/
theorem assembled_execution {n W V S T Q AP BI B : ℕ} (x : Fin n → ℂ)
    (v : ℕ → Fin V → Scalar) (y : Fin V → ℂ) (alpha betaInverse : Fin V ≃ Fin V)
    (s : State) (entry : Entry W V S T Q AP BI B v y alpha betaInverse s) :
    ∃u, Result W V S T Q v y alpha betaInverse u ∧
      BoundedExecution nativeProgram n x B {s with pc:=0} (27*V+28) {u with pc:=51} := by
  obtain ⟨u,joined,result⟩ := execution x v y alpha betaInverse s entry
  have fit : size stages≤B := by rw [stages_size];have h:=entry.code;omega
  have assembled := joined.execution fit
  refine ⟨u,result,?_⟩
  simpa only [nativeProgram,stages_size,Nat.add_assoc] using assembled

end
end ExactFourierCircuits.DFTModelOuterMiddle

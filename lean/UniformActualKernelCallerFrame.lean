import UniformKernelCallerStaticFrame
import UniformKernelChildCallerFrame
import UniformJointAllocationMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualKernelCallerFrame
open UniformMachine
noncomputable section
lemma corrected_parts:UniformRecursiveSavingProgram.order.length=46:=by rfl
/-- The independently checked corrected46-part child syntax discharges the
caller-frame premise of the literal initialized kernel; no child action needed. -/
theorem bounded_frame {W n B ticks:ℕ} {x:Fin n→ℂ} {s t:State}
 (run:BoundedExecution
  (UniformInitializedKernelExecution.programFor UniformRecursiveSavingProgram.program W) n x B s ticks t)
 (j:ℕ) (kept:6000≤j ∧j<6200 ∨6300≤j):t.natReg j=s.natReg j:=
 UniformKernelCallerStaticFrame.bounded_frame UniformKernelChildCallerFrame.program_safe run j kept

theorem allocated {W n B ticks:ℕ} {x:Fin n→ℂ} {s t:State}
 (run:BoundedExecution
  (UniformInitializedKernelExecution.programFor UniformRecursiveSavingProgram.program W) n x B s ticks t):
 UniformJointAllocationMachine.observed t=UniformJointAllocationMachine.observed s:=by
 unfold UniformJointAllocationMachine.observed
 congr 1 <;>exact bounded_frame run _ (Or.inl ⟨by omega,by omega⟩)

theorem calendar {W n B ticks:ℕ} {x:Fin n→ℂ} {s t:State}
 (run:BoundedExecution
  (UniformInitializedKernelExecution.programFor UniformRecursiveSavingProgram.program W) n x B s ticks t)
 (j:ℕ) (lo:6700≤j) (hi:j<6800):t.natReg j=s.natReg j:=by
 have _:=hi
 exact bounded_frame run j (Or.inr (by omega))
end
end ExactFourierCircuits.UniformActualKernelCallerFrame

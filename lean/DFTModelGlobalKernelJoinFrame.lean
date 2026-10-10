import DFTModelGlobalKernelJoinCore
import UniformKernelClockFrame
set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalKernelJoin
open UniformMachine UniformSyntacticNatFrame UniformClockCallerPrinterSafety
noncomputable section

/-- Existing exact syntax safety closes the full-pipeline conductor frame;
this includes the prefix, genuine child loop, inverse return and both halts. -/
theorem conductor_frame {F n i K prepTicks loopTicks returnTicks : ℕ} (c : KS.Context F)
 {v v0 : ℕ→Fin c.packing.volume→Scalar} {x : Fin n→ℂ}
 {s s0 a a0 t t0 z z0 : State} {trace : List ℕ}
 (h : DFTModelGlobalKernelSource.Result (i:=i) c v v0 K x s s0 a a0 t t0 z z0 prepTicks loopTicks returnTicks trace)
 (j : ℕ) (lo : 5920≤j) (hi : j<5940) :
 z.natReg j=s.natReg j ∧z0.natReg j=s0.natReg j := by
 have safe:=UniformKernelClockFrame.kernel_safe _ KS.W UniformRecursiveClockFrame.program_safe
 have first:=boundedExecution_preserves (safe_avoids safe j lo hi) h.actual
 have second:=boundedExecution_preserves (safe_avoids safe j lo hi) h.baseline
 exact ⟨first,second⟩

theorem startup_frame {F n i K prepTicks loopTicks returnTicks : ℕ} (c : KS.Context F)
 {v v0 : ℕ→Fin c.packing.volume→Scalar} {x : Fin n→ℂ}
 {s s0 a a0 t t0 z z0 : State} {trace : List ℕ}
 (h : DFTModelGlobalKernelSource.Result (i:=i) c v v0 K x s s0 a a0 t t0 z z0 prepTicks loopTicks returnTicks trace)
 (j : ℕ) (lo : 100≤j) (hi : j<107) :
 z.natReg j=s.natReg j ∧z0.natReg j=s0.natReg j := by
 have safe:=UniformKernelClockFrame.kernel_safe _ KS.W UniformRecursiveClockFrame.program_safe
 have first:=boundedExecution_preserves (safe_startup_avoids safe j lo hi) h.actual
 have second:=boundedExecution_preserves (safe_startup_avoids safe j lo hi) h.baseline
 exact ⟨first,second⟩

end
end ExactFourierCircuits.DFTModelGlobalKernelJoin

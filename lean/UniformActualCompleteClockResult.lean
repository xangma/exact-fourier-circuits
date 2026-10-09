import UniformFinalClockOuterFrame
import UniformFinalClockRuntime
import UniformActualClockEntry

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCompleteClockExecution
open UniformMachine
noncomputable section

/-- Observed complete-clock output required by the three-transform caller. -/
structure Output {n:ℕ}(hn:0<n)(x:Fin n→ℂ)
 (v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar)(s u:State):Prop where
 numeric:UniformActualClockEntry.Numeric n v u
 prepared:UniformActualClockEntry.Prepared v→UniformActualClockEntry.PreparedOutput n u
 retained:UniformFinalClockOuterRetention.Frame n s u
 spectrum:UniformFinalClockOuterRetention.Spectrum n s u
 runtime:UniformFinalClockRuntime.Runtime n u

end
end ExactFourierCircuits.UniformActualCompleteClockExecution

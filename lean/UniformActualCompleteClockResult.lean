import UniformFinalClockOuterFrame
import UniformFinalClockRuntime
import UniformActualClockEntry

/-!
Paper correspondence (audit): *An explicit power saving for the exact discrete Fourier transform*,
OpenAI math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
§4.3, Proposition 4.2 proof, PDF p. 20; §5.3, three charged transforms, p. 23.

This caller interface records numerical physical Fourier output, prepared tags, retained outer heaps and runtime allocation. Heap frames and tags have no one-to-one paper lemma; they certify composition with the outer three-transform argument.
-/

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

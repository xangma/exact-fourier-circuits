import DFTModelSavingNativeRoot

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeRoot
open OAI.PowerSaving OAI.PowerSaving.RAM
open UniformMachine
open DFTModelRecursiveScalarSource (paired)
noncomputable section
attribute [local irreducible] P.program DFTModelSavingProgram.program

/-- Any supplied terminated execution of the same source root has exactly
the constructed witness's ticks. An upper runtime budget is not substituted
for its measured instruction count. -/
theorem work_against_execution (n B k A F K ticks sourceTicks : ℕ) (x : Fin n→ℂ)
    (s s0 u u0 sourceFinal : State) (input input0 output output0 : Fin W→Fin (2^k)→Scalar)
    (result : Result n B k A F K x s s0 u u0 ticks input input0 output output0)
    (source : Executes P.program n x s sourceTicks sourceFinal) :
    (run DFTModelSavingProgram.program ((k,Complex.I),paired input input0)).work≤K*sourceTicks := by
  have same:=result.actual.executes.deterministic source
  rw [←same.1]
  exact result.work

end
end ExactFourierCircuits.DFTModelSavingNativeRoot

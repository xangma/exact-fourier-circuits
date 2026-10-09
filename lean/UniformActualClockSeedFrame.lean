import UniformActualGlobalClockProgram
import UniformKernelSeedFrame

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualClockSeedFrame
open UniformMachine UniformAssembly UniformSyntacticNatFrame UniformSeedCallerPrinterSafety
noncomputable section
attribute [local irreducible] UniformRecursiveSavingProgram.program

lemma diagonal_safe (W:ℕ):SafeProgram (UniformGlobalDiagonalReturn.programFor W):=by
 apply checked
 simp only[UniformGlobalDiagonalReturn.programFor,UniformGlobalTensorDiagonalPreparation.programFor,
  UniformGlobalDiagonalRowsMachine.program,UniformGlobalDiagonalPhasePreparation.program,
  UniformGlobalTensorDiagonalMachine.programFor,List.all_append,List.all_map,Function.comp_def,
  UniformKernelSeedFrame.relocate_safe_eq,List.all_cons,List.all_nil]
 rfl

lemma kernel_safe (W:ℕ):SafeProgram
 (UniformGlobalKernelDiagonalAssembly.programFor UniformRecursiveSavingProgram.program W):=by
 apply UniformKernelSeedFrame.assembly_safe
 · exact UniformKernelSeedFrame.initialized_safe _ W UniformRecursiveSeedFrame.program_safe
 · exact checked _ (by rfl)
 · exact diagonal_safe W

lemma conductor_safe (prepare child:Program) (W:ℕ)
 (hp:SafeProgram prepare)
 (hk:SafeProgram (UniformGlobalKernelDiagonalAssembly.programFor child W)):
 SafeProgram (UniformGlobalClockConductor.programFor prepare child W):=by
 unfold UniformGlobalClockConductor.programFor
 repeat' apply append_safe
 · exact checked _ (by rfl)
 · exact checked _ (by rfl)
 · exact checked _ (by rfl)
 · exact checked _ (by rfl)
 · exact relocated_safe hp _ _
 · apply relocated_safe
   exact checked _ (by decide +kernel)
 · apply relocated_safe
   exact checked _ (by rfl)
 · exact checked _ (by rfl)
 · exact checked _ (by rfl)
 · exact relocated_safe hk _ _
 · exact checked _ (by rfl)
 · exact checked _ (by rfl)

lemma program_safe:SafeProgram UniformActualGlobalClockProgram.program:=by
 apply conductor_safe
 · exact checked _ (by decide +kernel)
 · exact kernel_safe _

/-- The actual complete clock literal preserves the seed metadata registers.
The recursive program is checked through its finite pieces, never expanded. -/
theorem bounded_runs {n B ticks:ℕ}{x:Fin n→ℂ}{s t:State}
 (run:BoundedRuns UniformActualGlobalClockProgram.program n x B s ticks t)
 (j:ℕ)(lo:200≤j)(hi:j<210):t.natReg j=s.natReg j:=
 boundedRuns_preserves (safe_avoids program_safe j lo hi) run

theorem bounded_execution {n B ticks:ℕ}{x:Fin n→ℂ}{s t:State}
 (run:BoundedExecution UniformActualGlobalClockProgram.program n x B s ticks t)
 (j:ℕ)(lo:200≤j)(hi:j<210):t.natReg j=s.natReg j:=
 boundedExecution_preserves (safe_avoids program_safe j lo hi) run
end
end ExactFourierCircuits.UniformActualClockSeedFrame

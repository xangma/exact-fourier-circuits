import UniformGlobalKernelDiagonalAssembly
import UniformKernelClockFrame
import UniformActualKernelCallerFrame

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualTickCallerFrame
open UniformMachine UniformAssembly UniformSyntacticNatFrame
noncomputable section

lemma high_diagonal (W:ℕ):UniformKernelCallerPrinterSafety.SafeProgram
 (UniformGlobalDiagonalReturn.programFor W):=by
 apply UniformKernelCallerPrinterSafety.checked
 simp only[UniformGlobalDiagonalReturn.programFor,UniformGlobalTensorDiagonalPreparation.programFor,
  UniformGlobalDiagonalRowsMachine.program,UniformGlobalDiagonalPhasePreparation.program,
  UniformGlobalTensorDiagonalMachine.programFor,List.all_append,List.all_map,Function.comp_def,
  UniformKernelCallerStaticFrame.relocate_safe_eq,List.all_cons,List.all_nil]
 rfl
lemma clock_diagonal (W:ℕ):UniformClockCallerPrinterSafety.SafeProgram
 (UniformGlobalDiagonalReturn.programFor W):=by
 apply UniformClockCallerPrinterSafety.checked
 simp only[UniformGlobalDiagonalReturn.programFor,UniformGlobalTensorDiagonalPreparation.programFor,
  UniformGlobalDiagonalRowsMachine.program,UniformGlobalDiagonalPhasePreparation.program,
  UniformGlobalTensorDiagonalMachine.programFor,List.all_append,List.all_map,Function.comp_def,
  UniformKernelClockFrame.relocate_safe_eq,List.all_cons,List.all_nil]
 rfl
lemma high_program (W:ℕ):UniformKernelCallerPrinterSafety.SafeProgram
 (UniformGlobalKernelDiagonalAssembly.programFor UniformRecursiveSavingProgram.program W):=by
 apply UniformKernelCallerStaticFrame.assembly_safe
 · exact UniformKernelCallerStaticFrame.initialized_safe _ W UniformKernelChildCallerFrame.program_safe
 · exact UniformKernelCallerPrinterSafety.checked _ (by rfl)
 · exact high_diagonal W
lemma clock_program (W:ℕ):UniformClockCallerPrinterSafety.SafeProgram
 (UniformGlobalKernelDiagonalAssembly.programFor UniformRecursiveSavingProgram.program W):=by
 apply UniformKernelClockFrame.assembly_safe
 · exact UniformKernelClockFrame.initialized_safe _ W UniformRecursiveClockFrame.program_safe
 · exact UniformClockCallerPrinterSafety.checked _ (by rfl)
 · exact clock_diagonal W

theorem high {W n B ticks:ℕ}{x:Fin n→ℂ}{s t:State}
 (run:BoundedExecution
  (UniformGlobalKernelDiagonalAssembly.programFor UniformRecursiveSavingProgram.program W) n x B s ticks t)
 (j:ℕ)(kept:6000 ≤ j ∧j < 6200 ∨6300 ≤ j):t.natReg j=s.natReg j:=
 boundedExecution_preserves (UniformKernelCallerPrinterSafety.safe_avoids (high_program W) j kept) run

theorem clock {W n B ticks:ℕ}{x:Fin n→ℂ}{s t:State}
 (run:BoundedExecution
  (UniformGlobalKernelDiagonalAssembly.programFor UniformRecursiveSavingProgram.program W) n x B s ticks t)
 (j:ℕ)(lo:5920 ≤ j)(hi:j < 5940):t.natReg j=s.natReg j:=
 boundedExecution_preserves (UniformClockCallerPrinterSafety.safe_avoids (clock_program W) j lo hi) run

theorem startup {W n B ticks:ℕ}{x:Fin n→ℂ}{s t:State}
 (run:BoundedExecution
  (UniformGlobalKernelDiagonalAssembly.programFor UniformRecursiveSavingProgram.program W) n x B s ticks t)
 (j:ℕ)(lo:100 ≤ j)(hi:j < 107):t.natReg j=s.natReg j:=
 boundedExecution_preserves (UniformClockCallerPrinterSafety.safe_startup_avoids (clock_program W) j lo hi) run
end
end ExactFourierCircuits.UniformActualTickCallerFrame

import UniformSeedCallerPrinterSafety
import UniformRecursiveSavingProgram
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveSeedFrame
open UniformMachine UniformSyntacticNatFrame UniformSeedCallerPrinterSafety
namespace P
export UniformRecursiveSavingProgram (Part piece program order)
end P
noncomputable section

/-- These branches contain only finite helpers; neither literal payload is expanded. -/
lemma finite_piece_safe (a : P.Part) (seed:a≠.seedPrinter) (unit:a≠.unitPrinter) :
 SafeProgram (P.piece a) := by
 cases a <;> first | contradiction | exact checked _ (by decide +kernel)

lemma piece_safe (a : P.Part) : SafeProgram (P.piece a) := by
 by_cases seed:a=.seedPrinter
 · subst a
   exact relocated_safe fixed_decoder_safe _ _
 by_cases unit:a=.unitPrinter
 · subst a
   exact relocated_safe (printer_safe UniformRecursiveSavingProgram.unitRecord.data) _ _
 exact finite_piece_safe a seed unit

lemma program_safe : SafeProgram P.program := by
 intro i hi
 change i∈P.order.flatMap P.piece at hi
 obtain ⟨a,_,hi⟩:=List.mem_flatMap.mp hi
 exact piece_safe a i hi

lemma program_avoids (j : ℕ) (lo:200≤j)(hi:j<210) : Avoids P.program j :=
 safe_avoids program_safe j lo hi

theorem bounded_runs_frame {n B ticks : ℕ} {x : Fin n→ℂ} {s t : State}
 (run:BoundedRuns P.program n x B s ticks t) (j : ℕ)
 (lo:200≤j)(hi:j<210) : t.natReg j=s.natReg j :=
 boundedRuns_preserves (program_avoids j lo hi) run

theorem bounded_execution_frame {n B ticks : ℕ} {x : Fin n→ℂ} {s t : State}
 (run:BoundedExecution P.program n x B s ticks t) (j : ℕ)
 (lo:200≤j)(hi:j<210) : t.natReg j=s.natReg j :=
 boundedExecution_preserves (program_avoids j lo hi) run

end
end ExactFourierCircuits.UniformRecursiveSeedFrame

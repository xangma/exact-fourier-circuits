import UniformInitializedKernelExecution
import UniformRecursiveSeedFrame
import UniformSeedCallerPrinterSafety
set_option autoImplicit false
namespace ExactFourierCircuits.UniformKernelSeedFrame
open UniformMachine UniformAssembly UniformSyntacticNatFrame UniformSeedCallerPrinterSafety
noncomputable section
lemma relocate_safe_eq (b ret:ℕ) (i:Instruction):Safe (relocate b ret i)=Safe i:=by
 simp only[Safe,relocate_dst]
lemma movement_safe (W:ℕ):SafeProgram (UniformGlobalPackingChildPreparation.programFor W):=by
 apply checked
 simp only[UniformGlobalPackingChildPreparation.programFor,UniformGlobalMovementAssembly.assembly,
  List.all_append,List.all_map,Function.comp_def,relocate_safe_eq,
  UniformGlobalRolePackingMachine.programFor,UniformProducedSectorChildABI.programFor,UniformAssembly.embed,
  UniformProducedSectorTransposePreparation.programFor,UniformProducedSectorBatchPreparation.programFor,
  UniformMultiAxisSectorMetadataPreparation.program,UniformSectorBatchDirectoryMachine.programFor,
  UniformAllSectorTransposeMachine.programFor,List.all_cons,List.all_nil]
 rfl
lemma inverse_safe (W:ℕ):SafeProgram (UniformGlobalInverseReturn.programFor W):=by
 apply checked
 simp only[UniformGlobalInverseReturn.programFor,UniformProducedInversePacking.programFor,
  UniformGlobalMovementAssembly.assembly,UniformGlobalRoleScatterMachine.programFor,
  List.all_append,List.all_map,Function.comp_def,relocate_safe_eq,
  UniformAllSectorTransposeMachine.programFor,List.all_cons,List.all_nil]
 rfl
lemma loop_safe (child:Program) (safe:SafeProgram child):
 SafeProgram (UniformSameProgramSectorLoop.assembly child):=by
 unfold UniformSameProgramSectorLoop.assembly
 apply append_safe
 · apply append_safe
   · apply append_safe
     · apply append_safe
       · apply append_safe
         · exact checked _ (by rfl)
         · exact checked _ (by rfl)
       · exact checked _ (by rfl)
     · exact relocated_safe safe _ _
   · exact checked _ (by rfl)
 · exact checked _ (by rfl)
lemma assembly_safe (p q r:Program) (hp:SafeProgram p) (hq:SafeProgram q) (hr:SafeProgram r):
 SafeProgram (UniformGlobalMovementAssembly.assembly p q r):=by
 unfold UniformGlobalMovementAssembly.assembly
 exact append_safe (append_safe (append_safe (relocated_safe hp _ _) (relocated_safe hq _ _))
  (relocated_safe hr _ _)) halt_safe
lemma kernel_safe (child:Program) (W:ℕ) (safe:SafeProgram child):
 SafeProgram (UniformConditionalKernelLayout.programFor child W):=by
 apply assembly_safe
 · exact movement_safe W
 · apply assembly_safe
   · exact loop_safe child safe
   · exact inverse_safe W
   · intro i hi;simp at hi
 · intro i hi;simp at hi
lemma initialized_safe (child:Program) (W:ℕ) (safe:SafeProgram child):
 SafeProgram (UniformInitializedKernelExecution.programFor child W):=by
 unfold UniformInitializedKernelExecution.programFor
 exact append_safe (append_safe (checked _ (by rfl)) (relocated_safe (kernel_safe child W safe) _ _)) halt_safe
/-- A syntax-only caller frame for any actual execution of the literal full
kernel. Child syntax is checked independently; no readiness/value premise. -/
theorem bounded_frame {child:Program} {W n B ticks:ℕ} {x:Fin n→ℂ} {s t:State}
 (safe:SafeProgram child)
 (run:BoundedExecution (UniformInitializedKernelExecution.programFor child W) n x B s ticks t)
 (j:ℕ) (lo:200≤j)(hi:j<210):t.natReg j=s.natReg j:=
 boundedExecution_preserves (safe_avoids (initialized_safe child W safe) j lo hi) run

/-- Actual corrected-v2 child syntax closes the premise of the caller frame. -/
theorem actual_bounded_frame {W n B ticks:ℕ}{x:Fin n→ℂ}{s t:State}
 (run:BoundedExecution (UniformInitializedKernelExecution.programFor UniformRecursiveSavingProgram.program W) n x B s ticks t)
 (j:ℕ)(lo:200≤j)(hi:j<210):t.natReg j=s.natReg j:=
 bounded_frame UniformRecursiveSeedFrame.program_safe run j lo hi

theorem actual_bounded_runs_frame {W n B ticks:ℕ}{x:Fin n→ℂ}{s t:State}
 (run:BoundedRuns (UniformInitializedKernelExecution.programFor UniformRecursiveSavingProgram.program W) n x B s ticks t)
 (j:ℕ)(lo:200≤j)(hi:j<210):t.natReg j=s.natReg j:=
 boundedRuns_preserves (safe_avoids (initialized_safe _ W UniformRecursiveSeedFrame.program_safe) j lo hi) run
end
end ExactFourierCircuits.UniformKernelSeedFrame

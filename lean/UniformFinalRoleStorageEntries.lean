import UniformFinalRoleStorageCaller

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2 (5.5)-(5.6), PDF p.22, and §5.3 three-transform chirp
construction, PDF pp.22-23 (`eq:crt-fourier`, `eq:working-transform`, `eq:chirp`).

Role-bank, prepared-spectrum and movement bookkeeping refines the actual
three-transform algorithm. The paper does not specify these cells or registers;
all desired values must be obtained from the same actual producing executions.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalRoleStorageEntries
open UniformMachine UniformTensorMonomialMachine UniformFinalRoleModel UniformFinalClockCaller
open UniformFinalClockRuntime UniformFinalClockEntries
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants

/-- Strong first-clock caller retains the storage register produced by the real
role header, alongside the complete derived clock entry. -/
theorem kernel {n:ℕ} [NeZero (V n)] (hn:0<n) (x:Fin n→ℂ) (cacheEntry start s:State)
 (old:UniformFinalOuterStartup.Result n hn x cacheEntry start)
 (entry:UniformFinalPhysicalTablePrefix.Result n x s)
 (prefixFrame:UniformFinalPhysicalTablePrefix.Frame n start s)
 (wb:WordBound (UniformJointAllocation.envelope c n) s):∃u,
 UniformSequentialExecution.LocalStages n (UniformJointAllocation.envelope c n) x
  [UniformSequentialAssembly.natProgram (UniformFinalOuterHeaders.roleArgs W true),UniformRoleInputMachine.program] s
  (18+(5*(W*V n)+16*V n+24)) u∧
 Entry hn x (values x true (AP n)) (setPC u 0)∧
 UniformActualClockEntry.Prepared (values x true (AP n))∧
 UniformFinalNumericJoin.NumericValues (2*UniformJointAllocation.slab c n+V n)
  (fun j=>UniformFinalNumericJoin.kernel (n:=n) (AP n j)) u∧
 UniformFinalRoleExecution.Frame n s u∧u.natReg 7300=UniformKernelSpectrumStorage.base c n:=by
 obtain ⟨u,run,_up,source,prepared,numeric,frame,storage⟩:=
  UniformFinalRoleStorageCaller.kernel hn x s entry wb
 have runtime:=UniformFinalClockRuntime.of_prefix old entry prefixFrame
 have core:=(frame.core hn entry.core).withPC (pc:=0)
 have input:=UniformFinalClockRuntime.input hn x _ (setPC u 0) (runtime.role frame).pc
  core.metadata core.operands source rfl
  (changePC_bound _ u 0 (UniformFinalRoleCaller.LocalStages.bound run) (by omega))
 have retained:=UniformFinalClockCache.from_prefix hn old entry prefixFrame
 exact ⟨u,run,⟨input,UniformFinalClockCache.role_inputs_pc hn frame retained.1,
  UniformFinalClockCache.role_all_pc hn frame retained.2⟩,prepared,numeric,frame,storage⟩

/-- The data gather retains the freshly proved storage value, rather than
assuming that the role header left register7300 unchanged. -/
theorem data {n:ℕ} [NeZero (V n)] (hn:0<n) (x:Fin n→ℂ) (cacheEntry start s:State)
 (old:UniformFinalOuterStartup.Result n hn x cacheEntry start)
 (entry:UniformFinalPhysicalTablePrefix.Result n x s)
 (saved:∀q,Saved q→s.natReg q=start.natReg q)
 (cache:UniformAxisCacheLoopState.All c n hn (UniformAllAxisSeedPreparation.axisCount n) s)
 (wb:WordBound (UniformJointAllocation.envelope c n) s):∃u,
 UniformSequentialExecution.LocalStages n (UniformJointAllocation.envelope c n) x
  [UniformSequentialAssembly.natProgram (UniformFinalOuterHeaders.roleArgs W false),UniformRoleInputMachine.program,
   UniformPhysicalCRTConsumerMachine.alphaProgram] s
  (19+(5*(W*V n)+16*V n+24)+(9*V n+10)) u∧
 Entry hn x (UniformFinalRoleAlpha.physical x (AP n)) (setPC u 0)∧
 UniformFinalNumericJoin.NumericValues (2*UniformJointAllocation.slab c n)
  (fun j=>UniformFinalNumericJoin.data x (AP n j)) u∧
 UniformFinalRoleExecution.Frame n s u∧u.natReg 7300=UniformKernelSpectrumStorage.base c n:=by
 obtain ⟨u,run,_up,source,numeric,frame,storage⟩:=
  UniformFinalRoleStorageCaller.data hn x s entry wb
 have runtime:=UniformFinalClockCaller.from_saved old entry saved
 have core:=(frame.core hn entry.core).withPC (pc:=0)
 have input:=UniformFinalClockRuntime.input hn x _ (setPC u 0) (runtime.role frame).pc
  core.metadata core.operands source rfl
  (changePC_bound _ u 0 (UniformFinalRoleCaller.LocalStages.bound run) (by omega))
 exact ⟨u,run,⟨input,UniformFinalClockCache.role_inputs_pc hn frame (UniformAxisCacheInputs.of_core entry.core),
  UniformFinalClockCache.role_all_pc hn frame cache⟩,numeric,frame,storage⟩
end
end ExactFourierCircuits.UniformFinalRoleStorageEntries

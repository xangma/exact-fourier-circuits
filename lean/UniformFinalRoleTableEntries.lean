import UniformFinalRoleStorageEntries
import UniformFinalClockOuterDerivations
import UniformFinalClockOuterTable

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2 (5.5)-(5.6), PDF p.22, and §5.3 three-transform chirp
construction, PDF pp.22-23 (`eq:crt-fourier`, `eq:working-transform`, `eq:chirp`).

Role-bank, prepared-spectrum and movement bookkeeping refines the actual
three-transform algorithm. The paper does not specify these cells or registers;
all desired values must be obtained from the same actual producing executions.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalRoleTableEntries
open UniformMachine UniformTensorMonomialMachine UniformFinalRoleModel UniformFinalClockCaller
open UniformFinalClockEntries
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants

/-- Same actual kernel stages, with the retained physical table result and the
storage equation that the header genuinely produced. -/
theorem kernel {n:ℕ} [NeZero (V n)] (hn:0<n) (x:Fin n→ℂ) (cacheEntry start s:State)
 (old:UniformFinalOuterStartup.Result n hn x cacheEntry start)
 (entry:UniformFinalPhysicalTablePrefix.Result n x s)
 (prefixFrame:UniformFinalPhysicalTablePrefix.Frame n start s)
 (wb:WordBound (UniformJointAllocation.envelope c n) s):∃u,
 UniformSequentialExecution.LocalStages n (UniformJointAllocation.envelope c n) x
  [UniformSequentialAssembly.natProgram (UniformFinalOuterHeaders.roleArgs W true),UniformRoleInputMachine.program] s
  (18+(5*(W*V n)+16*V n+24)) u∧
 Entry hn x (values x true (AP n)) (setPC u 0)∧
 UniformFinalPhysicalTablePrefix.Result n x (setPC u 0)∧
 UniformActualClockEntry.Prepared (values x true (AP n))∧
 UniformFinalNumericJoin.NumericValues (2*UniformJointAllocation.slab c n+V n)
  (fun j=>UniformFinalNumericJoin.kernel (n:=n) (AP n j)) u∧
 UniformFinalClockOuterRetention.Frame n s u:=by
 obtain ⟨u,run,input,prepared,numeric,frame,storage⟩:=
  UniformFinalRoleStorageEntries.kernel hn x cacheEntry start s old entry prefixFrame wb
 have outer:=UniformFinalClockOuterRetention.Frame.role_of_table hn frame entry storage
 have table:=UniformFinalClockOuterRetention.Frame.table hn outer entry
 exact ⟨u,run,input,table.withPC,prepared,numeric,outer⟩

/-- Same actual data stages, preserving the physical AP/BI table result even
though the header rewrites7300 before the actual gather. -/
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
 UniformFinalPhysicalTablePrefix.Result n x (setPC u 0)∧
 UniformFinalNumericJoin.NumericValues (2*UniformJointAllocation.slab c n)
  (fun j=>UniformFinalNumericJoin.data x (AP n j)) u∧
 UniformFinalClockOuterRetention.Frame n s u:=by
 obtain ⟨u,run,input,numeric,frame,storage⟩:=
  UniformFinalRoleStorageEntries.data hn x cacheEntry start s old entry saved cache wb
 have outer:=UniformFinalClockOuterRetention.Frame.role_of_table hn frame entry storage
 have table:=UniformFinalClockOuterRetention.Frame.table hn outer entry
 exact ⟨u,run,input,table.withPC,numeric,outer⟩
end
end ExactFourierCircuits.UniformFinalRoleTableEntries

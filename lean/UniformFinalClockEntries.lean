import UniformFinalClockCaller
import UniformFinalClockCache

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §4.3 Proposition 4.2, PDF pp.19-20 (`prop:tensor-fourier`),
and §5.2 (5.6), PDF p.22 (`eq:working-transform`); integer/address accounting is §5.4, PDF p.24.

Retained physical-axis, cache and clock bookkeeping implements the costed
synchronized transform. These state/layout facts have no separate paper lemma;
their role is to discharge the actual caller's initialization and frame premises.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalClockEntries
open UniformMachine UniformTensorMonomialMachine UniformFinalRoleModel UniformFinalClockCaller
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants

/-- The real clock entry contains both scalar values and the cache/input facts
produced earlier by the charged startup. -/
structure Entry {n:ℕ} (hn:0<n) (x:Fin n→ℂ) (v:ℕ→Fin (V n)→Scalar) (s:State):Prop where
 input:UniformActualClockEntry.Input n (UniformFinalClockCaller.H n) (directory n) v s
 inputs:UniformAxisCacheInputs.Inputs n x s
 cache:UniformAxisCacheLoopState.All c n hn (UniformAllAxisSeedPreparation.axisCount n) s

lemma Entry.boot {n:ℕ} {hn:0<n} {x:Fin n→ℂ} {v:ℕ→Fin (V n)→Scalar} {s:State}
 (entry:Entry hn x v s):
 BoundedRuns UniformActualGlobalClockProgram.program n x (UniformJointAllocation.envelope c n)
  s 5 (applyBlock UniformGlobalClockConductor.boot s)∧
 UniformActualClockReady.Ready hn (UniformFinalClockCaller.H n) (directory n) x 0 v
  (applyBlock UniformGlobalClockConductor.boot s):=
 UniformActualClockReady.boot_execution hn x v s entry.input entry.inputs entry.cache

/-- Genuine prefix outputs imply the complete first-clock entry after the real
kernel header and role loader. No separate clock-ready state is assumed. -/
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
  (fun j=>UniformFinalNumericJoin.kernel (n:=n) (AP n j)) u∧UniformFinalRoleExecution.Frame n s u:=by
 obtain ⟨u,run,input,prepared,numeric,frame⟩:=
  UniformFinalClockCaller.kernel_from_prefix hn x cacheEntry start s old entry prefixFrame wb
 have source:=UniformFinalClockCache.from_prefix hn old entry prefixFrame
 exact ⟨u,run,⟨input,UniformFinalClockCache.role_inputs_pc hn frame source.1,
  UniformFinalClockCache.role_all_pc hn frame source.2⟩,prepared,numeric,frame⟩

/-- After an actual earlier clock preserves its cache and saved frontier fields,
the real data loader and AP gather derive the next complete clock entry. -/
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
  (fun j=>UniformFinalNumericJoin.data x (AP n j)) u∧UniformFinalRoleExecution.Frame n s u:=by
 obtain ⟨u,run,input,numeric,frame⟩:=
  UniformFinalClockCaller.data_from_saved hn x cacheEntry start s old entry saved wb
 exact ⟨u,run,⟨input,UniformFinalClockCache.role_inputs_pc hn frame (UniformAxisCacheInputs.of_core entry.core),
  UniformFinalClockCache.role_all_pc hn frame cache⟩,numeric,frame⟩
end
end ExactFourierCircuits.UniformFinalClockEntries

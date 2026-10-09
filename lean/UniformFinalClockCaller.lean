import UniformFinalClockRuntime

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §4.3 Proposition 4.2, PDF pp.19-20 (`prop:tensor-fourier`),
and §5.2 (5.6), PDF p.22 (`eq:working-transform`); integer/address accounting is §5.4, PDF p.24.

Retained physical-axis, cache and clock bookkeeping implements the costed
synchronized transform. These state/layout facts have no separate paper lemma;
their role is to discharge the actual caller's initialization and frame premises.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalClockCaller
open UniformMachine UniformTensorMonomialMachine UniformFinalRoleModel
open UniformFinalClockRuntime UniformFinalPhysicalTablePrefix
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants
abbrev H (n:ℕ):ℕ:=UniformFourierClockBounds.horizon n
abbrev directory (n:ℕ):ℕ:=UniformAllAxisSeedPreparation.directoryBase n
abbrev AP (n:ℕ):Fin (V n)≃Fin (V n):=UniformSelectedPhysicalCRT.physicalAlpha n

def Saved (q:ℕ):Prop:=q=5921∨q=6819∨q=6821∨q=6909∨q=6910
lemma from_saved {n:ℕ} {hn:0<n} {x:Fin n→ℂ} {cacheEntry start s:State}
 (old:UniformFinalOuterStartup.Result n hn x cacheEntry start)
 (entry:Result n x s) (saved:∀q,Saved q→s.natReg q=start.natReg q):Runtime n s:=by
 have allocated:=UniformJointAllocationMachine.observed_eq s (UniformJointAllocation.slab c n) entry.headers
 refine ⟨allocated,(saved _ (by unfold Saved;omega)).trans old.cache.clock,
  (saved _ (by unfold Saved;omega)).trans old.cache.natEnd,
  (saved _ (by unfold Saved;omega)).trans old.cache.scalarEnd,entry.source,?_,?_⟩
 · have h:=(saved _ (by unfold Saved;omega)).trans old.cache.savedNat
   simpa only[UniformAxisCacheSelectedPreparation.natAt,UniformJointCacheAllocation.offsetSum,Finset.range_zero,Finset.sum_empty,Nat.add_zero]using h
 · have h:=(saved _ (by unfold Saved;omega)).trans old.cache.savedScalar
   simpa only[UniformAxisCacheSelectedPreparation.scalarAt,UniformJointCacheAllocation.offsetSum,Finset.range_zero,Finset.sum_empty,Nat.add_zero]using h
lemma from_input {n:ℕ} {v:ℕ→Fin (V n)→Scalar} {s:State}
 (h:UniformActualClockEntry.Input n (H n) (directory n) v s):Runtime n s:=
 ⟨h.allocator,h.horizon,h.natFrontier,h.scalarFrontier,h.seed,h.initialNat,h.initialScalar⟩

/-- The full kernel clock entry is derived after the actual charged role runs. -/
theorem kernel {n:ℕ} [NeZero (V n)] (hn:0<n) (x:Fin n→ℂ) (s:State)
 (entry:Result n x s) (runtime:Runtime n s) (wb:WordBound (UniformJointAllocation.envelope c n) s):∃u,
 UniformSequentialExecution.LocalStages n (UniformJointAllocation.envelope c n) x
  [UniformSequentialAssembly.natProgram (UniformFinalOuterHeaders.roleArgs W true),UniformRoleInputMachine.program] s
  (18+(5*(W*V n)+16*V n+24)) u∧
 UniformActualClockEntry.Input n (H n) (directory n) (values x true (AP n)) (setPC u 0)∧
 UniformActualClockEntry.Prepared (values x true (AP n))∧
 UniformFinalNumericJoin.NumericValues (2*UniformJointAllocation.slab c n+V n)
  (fun j=>UniformFinalNumericJoin.kernel (n:=n) (AP n j)) u∧UniformFinalRoleExecution.Frame n s u:=by
 obtain ⟨u,run,_up,source,prepared,numeric,frame⟩:=UniformFinalRoleCaller.kernel hn x s entry wb
 have core:=(frame.core hn entry.core).withPC (pc:=0)
 have input:=UniformFinalClockRuntime.input hn x _ (setPC u 0) (runtime.role frame).pc
  core.metadata core.operands source rfl
  (changePC_bound _ u 0 (UniformFinalRoleCaller.LocalStages.bound run) (by omega))
 exact ⟨u,run,input,prepared,numeric,frame⟩

/-- The full data clock entry follows the actual loader and actual AP gather. -/
theorem data {n:ℕ} [NeZero (V n)] (hn:0<n) (x:Fin n→ℂ) (s:State)
 (entry:Result n x s) (runtime:Runtime n s) (wb:WordBound (UniformJointAllocation.envelope c n) s):∃u,
 UniformSequentialExecution.LocalStages n (UniformJointAllocation.envelope c n) x
  [UniformSequentialAssembly.natProgram (UniformFinalOuterHeaders.roleArgs W false),UniformRoleInputMachine.program,
   UniformPhysicalCRTConsumerMachine.alphaProgram] s
  (19+(5*(W*V n)+16*V n+24)+(9*V n+10)) u∧
 UniformActualClockEntry.Input n (H n) (directory n) (UniformFinalRoleAlpha.physical x (AP n)) (setPC u 0)∧
 UniformFinalNumericJoin.NumericValues (2*UniformJointAllocation.slab c n)
  (fun j=>UniformFinalNumericJoin.data x (AP n j)) u∧UniformFinalRoleExecution.Frame n s u:=by
 obtain ⟨u,run,_up,source,numeric,frame⟩:=UniformFinalRoleCaller.data hn x s entry wb
 have core:=(frame.core hn entry.core).withPC (pc:=0)
 have input:=UniformFinalClockRuntime.input hn x _ (setPC u 0) (runtime.role frame).pc
  core.metadata core.operands source rfl
  (changePC_bound _ u 0 (UniformFinalRoleCaller.LocalStages.bound run) (by omega))
 exact ⟨u,run,input,numeric,frame⟩

/-- The first caller needs only the actual prefix outputs and their actual
saved-register frame; there is no separate clock-ready input premise. -/
theorem kernel_from_prefix {n:ℕ} [NeZero (V n)] (hn:0<n) (x:Fin n→ℂ) (cacheEntry start s:State)
 (old:UniformFinalOuterStartup.Result n hn x cacheEntry start) (entry:Result n x s)
 (frame:Frame n start s) (wb:WordBound (UniformJointAllocation.envelope c n) s):∃u,
 UniformSequentialExecution.LocalStages n (UniformJointAllocation.envelope c n) x
  [UniformSequentialAssembly.natProgram (UniformFinalOuterHeaders.roleArgs W true),UniformRoleInputMachine.program] s
  (18+(5*(W*V n)+16*V n+24)) u∧
 UniformActualClockEntry.Input n (H n) (directory n) (values x true (AP n)) (setPC u 0)∧
 UniformActualClockEntry.Prepared (values x true (AP n))∧
 UniformFinalNumericJoin.NumericValues (2*UniformJointAllocation.slab c n+V n)
  (fun j=>UniformFinalNumericJoin.kernel (n:=n) (AP n j)) u∧UniformFinalRoleExecution.Frame n s u:=
 kernel hn x s entry (of_prefix old entry frame) wb

/-- Later data entry uses the original produced cache clock/frontiers transported
through actual saved-register equality, then constructs its own scalar source. -/
theorem data_from_saved {n:ℕ} [NeZero (V n)] (hn:0<n) (x:Fin n→ℂ) (cacheEntry start s:State)
 (old:UniformFinalOuterStartup.Result n hn x cacheEntry start) (entry:Result n x s)
 (saved:∀q,Saved q→s.natReg q=start.natReg q) (wb:WordBound (UniformJointAllocation.envelope c n) s):∃u,
 UniformSequentialExecution.LocalStages n (UniformJointAllocation.envelope c n) x
  [UniformSequentialAssembly.natProgram (UniformFinalOuterHeaders.roleArgs W false),UniformRoleInputMachine.program,
   UniformPhysicalCRTConsumerMachine.alphaProgram] s
  (19+(5*(W*V n)+16*V n+24)+(9*V n+10)) u∧
 UniformActualClockEntry.Input n (H n) (directory n) (UniformFinalRoleAlpha.physical x (AP n)) (setPC u 0)∧
 UniformFinalNumericJoin.NumericValues (2*UniformJointAllocation.slab c n)
  (fun j=>UniformFinalNumericJoin.data x (AP n j)) u∧UniformFinalRoleExecution.Frame n s u:=
 data hn x s entry (from_saved old entry saved) wb
end
end ExactFourierCircuits.UniformFinalClockCaller

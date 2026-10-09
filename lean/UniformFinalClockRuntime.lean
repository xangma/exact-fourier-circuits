import UniformFinalClockLength
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalClockRuntime
open UniformMachine UniformTensorMonomialMachine UniformFinalRoleModel
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants
/-- Ordinary retained allocator/clock registers, separated from the scalar
source so they can survive actual numerical calls. -/
structure Runtime (n:ℕ) (s:State):Prop where
 allocator:UniformJointAllocationMachine.observed s=UniformJointAllocation.allocate c n
 horizon:s.natReg 5921=UniformFourierClockBounds.horizon n
 natEnd:s.natReg 6819=UniformGlobalCalendarArena.natBase c n
 scalarEnd:s.natReg 6821=UniformGlobalCalendarArena.scalarBase c n
 seed:s.natReg 6904=UniformAllAxisSeedPreparation.directoryBase n
 initialNat:s.natReg 6909=UniformJointCacheAllocation.natStart c n
 initialScalar:s.natReg 6910=UniformJointCacheAllocation.scalarStart c n

def Kept (q:ℕ):Prop:=(6020≤q∧q≤6037)∨q=5921∨q=6819∨q=6821∨q=6904∨q=6909∨q=6910
lemma Runtime.transport {n:ℕ} {s u:State} (h:Runtime n s)
 (eq:∀q,Kept q→u.natReg q=s.natReg q):Runtime n u:=by
 have allocator:UniformJointAllocationMachine.observed u=UniformJointAllocationMachine.observed s:=by
  unfold UniformJointAllocationMachine.observed
  congr 1
  all_goals exact eq _ (by unfold Kept;omega)
 exact ⟨allocator.trans h.allocator,
  (eq _ (by unfold Kept;omega)).trans h.horizon,
  (eq _ (by unfold Kept;omega)).trans h.natEnd,
  (eq _ (by unfold Kept;omega)).trans h.scalarEnd,
  (eq _ (by unfold Kept;omega)).trans h.seed,
  (eq _ (by unfold Kept;omega)).trans h.initialNat,
  (eq _ (by unfold Kept;omega)).trans h.initialScalar⟩
lemma Runtime.role {n:ℕ} {s u:State} (h:Runtime n s) (f:UniformFinalRoleExecution.Frame n s u):Runtime n u:=by
 apply h.transport
 intro q hq
 exact f.natReg q (by unfold UniformFinalRoleExecution.R.Protected;unfold Kept at hq;omega)
  (by unfold UniformFinalRoleExecution.H.Changed;unfold Kept at hq;omega)
lemma Runtime.pc {n p:ℕ} {s:State} (h:Runtime n s):Runtime n (setPC s p):=
 ⟨h.allocator,h.horizon,h.natEnd,h.scalarEnd,h.seed,h.initialNat,h.initialScalar⟩

/-- These register values are consequences of the genuine cache producer and
its actual table-prefix frame, not an independent clock entry assumption. -/
lemma of_prefix {n:ℕ} {hn:0<n} {x:Fin n→ℂ} {cacheEntry start s:State}
 (old:UniformFinalOuterStartup.Result n hn x cacheEntry start)
 (entry:UniformFinalPhysicalTablePrefix.Result n x s)
 (frame:UniformFinalPhysicalTablePrefix.Frame n start s):Runtime n s:=by
 have allocated:=UniformJointAllocationMachine.observed_eq s (UniformJointAllocation.slab c n) entry.headers
 have keep(q:ℕ)(hq:q=5921∨q=6819∨q=6821∨q=6909∨q=6910):s.natReg q=start.natReg q:=
  frame.natReg q (by unfold UniformPhysicalCRTTableHeaders.Changed;omega) (Or.inl (by omega))
 refine ⟨allocated,(keep _ (by omega)).trans old.cache.clock,
  (keep _ (by omega)).trans old.cache.natEnd,(keep _ (by omega)).trans old.cache.scalarEnd,
  entry.source,?_,?_⟩
 · have h:=(keep _ (by omega)).trans old.cache.savedNat
   simpa only[UniformAxisCacheSelectedPreparation.natAt,UniformJointCacheAllocation.offsetSum,Finset.range_zero,Finset.sum_empty,Nat.add_zero]using h
 · have h:=(keep _ (by omega)).trans old.cache.savedScalar
   simpa only[UniformAxisCacheSelectedPreparation.scalarAt,UniformJointCacheAllocation.offsetSum,Finset.range_zero,Finset.sum_empty,Nat.add_zero]using h
lemma constants {n:ℕ} {x:Fin n→ℂ} {s:State} (h:UniformInitialPreparation.Operands n x s):UniformBinaryCStageMachine.Constants s:=by
 constructor
 · simpa [UniformCConstantsMachine.bank] using h.constants (1:Fin 6)
 · simpa [UniformCConstantsMachine.bank] using h.constants (2:Fin 6)

lemma input {n:ℕ} (hn:0<n) (x:Fin n→ℂ) (v:ℕ→Fin (V n)→Scalar) (s:State)
 (runtime:Runtime n s) (metadata:UniformPermutationInversePreparation.Metadata n s)
 (operands:UniformInitialPreparation.Operands n x s) (source:UniformActualClockEntry.Source n v s)
 (pc:s.pc=0) (wb:WordBound (UniformJointAllocation.envelope c n) s):
 UniformActualClockEntry.Input n (UniformFourierClockBounds.horizon n)
  (UniformAllAxisSeedPreparation.directoryBase n) v s:=by
 refine ⟨pc,wb,UniformFinalClockLength.code n,runtime.allocator,?_,metadata.saved.workingLength,
  runtime.horizon,runtime.natEnd,runtime.scalarEnd,runtime.seed,runtime.initialNat,runtime.initialScalar,
  source,constants operands,UniformFinalClockLength.local_length hn⟩
 rw[metadata.saved.count]
end
end ExactFourierCircuits.UniformFinalClockRuntime

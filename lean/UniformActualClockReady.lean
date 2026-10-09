import UniformActualClockEntry
import UniformActualClockBoundaryExecution
import UniformClockCacheInputsRetention
import UniformAxisCacheLoopState
set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualClockReady
open UniformMachine UniformGlobalClockConductor
open UniformAllAxisSeedPreparation (axisCount)
open UniformActualGlobalConstants (constants)
open UniformTensorMonomialMachine (applyBlock Op)
noncomputable section
attribute [local irreducible] UniformRecursiveSavingProgram.program

/-- The actual horizon invariant at the literal clock test. Cache contents and
ordinary input tables come from their charged producers and survive each tick. -/
structure Ready {n:ℕ} (hn:0<n) (H seedDirectory:ℕ) (x:Fin n→ℂ) (t:ℕ)
 (v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar) (s:State):Prop where
 pc:s.pc=5
 bound:WordBound (UniformJointAllocation.envelope constants n) s
 allocator:UniformJointAllocationMachine.observed s=UniformJointAllocation.allocate constants n
 axisCount:s.natReg 102+1=UniformAllAxisSeedPreparation.axisCount n
 volume:s.natReg 103=UniformActualClockEntry.volume n
 horizon:s.natReg 5921=H
 clock:s.natReg 5920=t
 natArena:s.natReg 5936=UniformGlobalCalendarArena.natBase constants n
 scalarArena:s.natReg 5937=UniformGlobalCalendarArena.scalarBase constants n
 axes:s.natReg 5938=UniformAllAxisSeedPreparation.axisCount n
 one:s.natReg 5939=1
 seed:s.natReg 6904=seedDirectory
 initialNat:s.natReg 6909=UniformJointCacheAllocation.natStart constants n
 initialScalar:s.natReg 6910=UniformJointCacheAllocation.scalarStart constants n
 source:UniformActualClockEntry.Source n v s
 constants:UniformBinaryCStageMachine.Constants s
 length:∀i,(UniformSynchronizedLayers.localSchedules n i).length≤H
 inputs:UniformAxisCacheInputs.Inputs n x s
 cache:UniformAxisCacheLoopState.All UniformActualGlobalConstants.constants n hn (UniformAllAxisSeedPreparation.axisCount n) s

lemma boot_kept (s:State) (j:ℕ) (a:j≠5920) (b:j≠5936) (c:j≠5937) (d:j≠5938) (e:j≠5939):
 (applyBlock boot s).natReg j=s.natReg j:=by
 simp[boot,applyBlock,Op.apply,UniformMachine.writeNat,UniformMachine.next,a,b,c,d,e]


/-- The charged five-instruction clock boot establishes the genuine invariant. -/
theorem boot_execution {n H seedDirectory:ℕ} (hn:0<n) (x:Fin n→ℂ)
 (v:ℕ→Fin (UniformActualClockEntry.volume n)→Scalar) (s:State)
 (entry:UniformActualClockEntry.Input n H seedDirectory v s)
 (inputs:UniformAxisCacheInputs.Inputs n x s)
 (cache:UniformAxisCacheLoopState.All UniformActualGlobalConstants.constants n hn (UniformAllAxisSeedPreparation.axisCount n) s):
 BoundedRuns UniformActualGlobalClockProgram.program n x (UniformJointAllocation.envelope constants n)
  s 5 (applyBlock boot s) ∧Ready hn H seedDirectory x 0 v (applyBlock boot s):=by
 have count:s.natReg 102+1≤UniformJointAllocation.envelope constants n:=by
  rw[entry.axisCount]
  have small:=UniformJointAllocation.actual_arithmetic constants n hn
  unfold UniformJointAllocation.envelope
  omega
 obtain ⟨run,pc,clock,horizon,natArena,scalarArena,axes,one⟩:=
  UniformActualClockBoundaryExecution.boot_execution x s entry.pc entry.code count entry.bound
 have heaps:=UniformGlobalClockControl.heap_frame s boot (Or.inl rfl)
 have regs(q:ℕ)(lo:100≤q)(hi:q<107):(applyBlock boot s).natReg q=s.natReg q:=
  boot_kept s q (by omega) (by omega) (by omega) (by omega) (by omega)
 have input:=UniformClockCacheInputsRetention.inputs constants hn x s (applyBlock boot s) inputs
  (fun q _=>congrFun heaps.1 q) (fun q _=>congrFun heaps.2.1 q) (fun q lo hi=>regs q lo (by omega)) heaps.2.2.2.1 heaps.2.2.2.2
 have allocated:UniformJointAllocationMachine.observed (applyBlock boot s)=UniformJointAllocationMachine.observed s:=by
  unfold UniformJointAllocationMachine.observed
  rfl
 refine ⟨run,pc,run.final_bound,allocated.trans entry.allocator,?_,?_,horizon.trans entry.horizon,clock,
  natArena.trans entry.natFrontier,scalarArena.trans entry.scalarFrontier,axes.trans entry.axisCount,one,
  ?_,?_,?_,?_,?_,entry.length,input,UniformAxisCacheLoopState.All.transport cache heaps.1 heaps.2.1⟩
 · exact (regs 102 (by omega) (by omega)) ▸ entry.axisCount
 · exact (regs 103 (by omega) (by omega)).trans entry.volume
 · exact (boot_kept s 6904 (by omega) (by omega) (by omega) (by omega) (by omega)).trans entry.seed
 · exact (boot_kept s 6909 (by omega) (by omega) (by omega) (by omega) (by omega)).trans entry.initialNat
 · exact (boot_kept s 6910 (by omega) (by omega) (by omega) (by omega) (by omega)).trans entry.initialScalar
 · intro r hr j;rw[heaps.2.1];exact entry.source r hr j
 · exact entry.constants
end
end ExactFourierCircuits.UniformActualClockReady

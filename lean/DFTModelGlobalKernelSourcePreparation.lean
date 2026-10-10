import DFTModelGlobalKernelSourceCore
set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalKernelSource
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (setPC)
open DFTModelAdmissibilityControl
noncomputable section

structure Prefix {F n i : ℕ} (c : Context F) (v : ℕ→Fin c.packing.volume→Scalar)
 (x : Fin n→ℂ) (s u : State) (ticks : ℕ) : Prop where
 actual : BoundedExecution (UniformGlobalPackingChildPreparation.programFor W) n x c.metadata.B s ticks u
 cheap : ticks ≤ UniformConditionalKernelLayout.movementCost c
 pc : u.pc=371
 filled : UniformAllSectorTransposeMachine.Filled c.gather (UniformConditionalKernelLayout.packed c v) (states c).length u
 table : UniformAllSectorTransposeMachine.Table c.gather u
 count : u.natReg 464=(states c).length
 directory : u.natReg 4441=c.gather.directory
 frontier : u.natReg 5801=F
 scalarBefore : ∀q,q<c.packing.destination→q<c.gather.buffer→u.scalarHeap q=s.scalarHeap q
 natBefore : ∀q,q<c.packing.suffix→q<c.metadata.rows→u.natHeap q=s.natHeap q
 inverse : UniformGlobalInverseReturn.Args c.inverse c.scatter.directory u
 constants : UniformBinaryCStageMachine.Constants u
 banks : UniformGlobalRolePackingMachine.Banks c.packing c.physical u
 outputs : u.outputs=s.outputs
 roots : u.rootOrders=s.rootOrders

/-- Real153 packing followed by the real218 generated all-gather/child-ABI
prefix. The prefix consumes the original physical widths/permutations and
produces every gathered sector before any recursive child is entered. -/
theorem prefix_execution {F n i : ℕ} (c : Context F) (v : ℕ→Fin c.packing.volume→Scalar)
 (x : Fin n→ℂ) (s : State) (h : UniformConditionalKernelLayout.Ready c i v s)
 (hi : i<(states c).length) (code : 372≤c.metadata.B) (pc : s.pc=0) (wb : WordBound c.metadata.B s) :
 ∃u ticks,Prefix (i:=i) c v x s u ticks := by
 obtain ⟨u,ticks,run,cheap,up,_child,_pow,_grouped,filled,table,count,dir,fresh,
  _saved,out,roots,scalar,nat,kept⟩ := UniformKernelPreparationRetention.execution
  c.packing c.physical c.physicalVolume c.physicalLength c.metadata c.gather v x s
  c.packingB c.gatherB c.packingVolume c.gatherVolume c.gatherSource c.metadataLength
  h.packing h.banks c.widthsBelow c.permutationsBelow c.widthsMetadata c.rowsMetadata
  c.entry c.directory code h.count h.axes h.metadataRows h.suffix h.stack h.directory
  h.batchDirectory h.childBank h.native h.volume h.source hi h.ordinal h.frontier pc wb
 have inverse : UniformGlobalInverseReturn.Args c.inverse c.scatter.directory u :=
  UniformConditionalSectorReturn.args_transfer c.inverse s u h.inverse kept
 have constants : UniformBinaryCStageMachine.Constants u := by
  have sep := c.gather.separation
  simp only[Bool.false_eq_true,ite_false,c.gatherSource] at sep
  have low := c.scalarLow
  constructor
  · exact (scalar 1 (by omega) (by omega)).trans h.constants.1
  · exact (scalar 2 (by omega) (by omega)).trans h.constants.2
 have banks : UniformGlobalRolePackingMachine.Banks c.packing c.physical u := by
  refine ⟨?_,?_,?_⟩
  · apply UniformConditionalSectorReturn.rows_prefix c.physical 0 c.packing.rows
      (min c.packing.suffix c.metadata.rows) s u h.banks.1
    · have p:=c.packing.rowsBelow
      have q:=c.rowsMetadata
      rw[c.physicalLength] at *
      exact Nat.le_min.mpr ⟨by simpa only[Nat.zero_add] using p,
       by simpa only[Nat.zero_add,←c.physicalLength,c.metadataLength] using q⟩
    · intro q hq;exact nat q (lt_of_lt_of_le hq (Nat.min_le_left _ _))
        (lt_of_lt_of_le hq (Nat.min_le_right _ _))
  · intro a ha j
    exact (nat _ (by have:=c.widthsBelow a ha;omega)
      (by have:=c.widthsMetadata a ha;omega)).trans (h.banks.2.1 a ha j)
  · intro a ha j
    exact (nat _ (by have:=c.permutationsBelow a ha;omega)
      (by have:=c.permutationsMetadata a ha;omega)).trans (h.banks.2.2 a ha j)
 exact ⟨u,ticks,run,cheap,up,filled,table,count,dir,fresh,scalar,nat,inverse,constants,banks,out,roots⟩

structure Preparation {F n i : ℕ} (c : Context F) (v v0 : ℕ→Fin c.packing.volume→Scalar)
 (x : Fin n→ℂ) (s s0 u u0 : State) (ticks : ℕ) : Prop where
 actual : Prefix (i:=i) c v x s u ticks
 baseline : Prefix (i:=i) c v0 (fun _ : Fin n=>0) s0 u0 ticks
 matched : StateMatch u u0
 pending : DFTModelGlobalSectorLoop.Pending c.gather.buffer (states c) (UniformConditionalKernelLayout.packed c v) 0 u
 pending0 : DFTModelGlobalSectorLoop.Pending c.gather.buffer (states c) (UniformConditionalKernelLayout.packed c v0) 0 u0

/-- Both real data channels use one instruction count. The second witness is
constructed by the same original prefix, and determinism identifies its ticks
with the operational counterpart of the first witness. -/
theorem preparation {F n i : ℕ} (c : Context F) (v v0 : ℕ→Fin c.packing.volume→Scalar)
 (x : Fin n→ℂ) (s s0 : State) (same : StateMatch s s0)
 (h : UniformConditionalKernelLayout.Ready c i v s)
 (source0 : UniformGlobalRolePackingMachine.Source c.packing v0 s0)
 (hi : i<(states c).length) (code : 372≤c.metadata.B) (pc : s.pc=0) (wb : WordBound c.metadata.B s) :
 ∃u u0 ticks,Preparation (i:=i) c v v0 x s s0 u u0 ticks := by
 obtain ⟨u,ticks,a⟩:=prefix_execution c v x s h hi code pc wb
 obtain ⟨u0,ticks0,z⟩:=prefix_execution c v0 (fun _ : Fin n=>0) s0 (ready_match v v0 same h source0)
  hi code (same.pc.trans pc) (same.wordBound wb)
 obtain ⟨t0,pairedRun,matched⟩:=boundedExecution_match (y:=fun _ : Fin n=>0) a.actual same
 obtain ⟨eqTicks,eqState⟩:=pairedRun.executes.deterministic z.actual.executes
 subst ticks0
 subst t0
 exact ⟨u,u0,ticks,a,z,matched,filled_pending c _ u a.filled,filled_pending c _ u0 z.filled⟩
end
end ExactFourierCircuits.DFTModelGlobalKernelSource

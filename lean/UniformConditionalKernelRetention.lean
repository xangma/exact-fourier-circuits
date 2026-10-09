import UniformConditionalKernelExecution
import UniformConditionalSectorReturnRetention
set_option autoImplicit false
namespace ExactFourierCircuits.UniformConditionalKernelRetention
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (setPC)
open UniformSectorPackingMachine (Rows Widths Permutations)
open UniformConditionalKernelLayout (Context Ready packed movementCost programFor)
noncomputable section
/-- Genuine persistent cache prefixes pass through actual153→218→finite
same-child sectors→220. Only the same internal child RootBody remains assumed. -/
theorem execution {W F reserve n ordinal:ℕ} (child:Program) (c:Context W F reserve)
 (cost:ℕ → ℕ) (v:ℕ → Fin c.packing.volume → Scalar) (x:Fin n → ℂ) (s:State)
 (ready:Ready c ordinal v s) (hi:ordinal < (UniformProducedSectorChildABI.states c.physical).length)
 (root:UniformConditionalSectorLoop.RootBody child W n c.inverse.layout.B F reserve cost x)
 (positive:0 < W) (code:child.length+614 ≤ c.metadata.B) (pc:s.pc=0) (wb:WordBound c.metadata.B s):
 ∃mid u ticks,UniformConditionalSectorLoop.Completed W c.gather.buffer
  (UniformProducedSectorChildABI.states c.physical) (packed c v)
  (UniformProducedSectorChildABI.states c.physical).length mid ∧
 BoundedExecution (programFor child W) n x c.metadata.B s ticks u ∧
 ticks ≤ movementCost c+UniformConditionalSectorLoop.budget cost (UniformProducedSectorChildABI.states c.physical)+
  213*c.inverse.layout.total+W*(16*c.inverse.layout.total+12)+
  (12*W+20)*(UniformProducedSectorChildABI.states c.physical).length+57 ∧u.pc=child.length+613 ∧
 (∀r,r < W → ∀j:Fin c.inverse.layout.total,u.scalarHeap (c.inverse.destination+r*c.inverse.layout.total+j.val)=some
  (UniformSectorPayloadBridge.payload (UniformSectorPayloadBridge.actual_cover c.physical c.loop.volume
   ((c.physicalVolume.trans c.inverseVolume).trans c.loopVolume.symm)) W c.gather.buffer mid r
   ((UniformSectorPackingMachine.physicalUnpacking c.physical c.inverse.layout
    (c.physicalVolume.trans c.inverseVolume)).symm j).val)) ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,q < c.packing.suffix → q < c.metadata.rows → q < F →
  q < c.inverse.layout.stack → q < c.inverse.layout.inverse → u.natHeap q=s.natHeap q) ∧
 (∀q,q < c.packing.destination → q < c.gather.buffer → q < F → q < c.scatter.native →
  q < c.inverse.layout.destination → q < c.inverse.destination → u.scalarHeap q=s.scalarHeap q):=by
 obtain ⟨t,first,firstRun,cheap,tp,childHeader,pow,grouped,filled,table,count,dir,fresh,saved,outputs,roots,scalar,nat,args⟩:=
  UniformKernelPreparationRetention.execution c.packing c.physical c.physicalVolume c.physicalLength c.metadata
   c.gather v x s c.packingB c.gatherB c.packingVolume c.gatherVolume c.gatherSource c.metadataLength
   ready.packing ready.banks c.widthsBelow c.permutationsBelow c.widthsMetadata c.rowsMetadata c.entry c.directory
   (by omega) ready.count ready.axes ready.metadataRows ready.suffix ready.stack ready.directory
   ready.batchDirectory ready.childBank ready.native ready.volume ready.source hi ready.ordinal ready.frontier pc wb
 have moved:=UniformBoundedAssembly.boundedExecution_placed (UniformConditionalKernelLayout.movement_code child W)
  (by rw[UniformGlobalPackingChildPreparation.program_length];omega) (by omega) firstRun
 rw[show placed 0 s=s by cases s;simp[placed]] at moved
 let entry:=setPC t 0
 have eb:WordBound c.inverse.layout.B entry:=by
  rw[c.inverseB]
  exact changePC_bound c.metadata.B t 0 firstRun.final_bound (by omega)
 have argsE:UniformGlobalInverseReturn.Args c.inverse c.scatter.directory entry:=
  UniformConditionalSectorReturn.args_transfer c.inverse s entry ready.inverse args
 have constants:UniformBinaryCStageMachine.Constants entry:=by
  constructor
  · exact (scalar 1 (by have:=c.scalarLow;omega) (by have:=c.loop.low;omega)).trans ready.constants.1
  · exact (scalar 2 (by have:=c.scalarLow;omega) (by have:=c.loop.low;omega)).trans ready.constants.2
 have tableE:UniformConditionalSectorLoop.Table W c.gather.directory c.gather.buffer
  (UniformProducedSectorChildABI.states c.physical) entry:=table
 have pending:UniformConditionalSectorLoop.Pending W c.gather.buffer
  (UniformProducedSectorChildABI.states c.physical) (packed c v) 0 entry:=by
  intro i h le r hr t ht
  exact filled i h h r hr t ht
 have rowBound:c.packing.rows+4*c.physical.length ≤ c.packing.suffix:=by
  rw[c.physicalLength];exact c.packing.rowsBelow
 have rowMeta:c.packing.rows+4*c.physical.length ≤ c.metadata.rows:=by
  rw[c.metadataLength];exact c.rowsMetadata
 have rowsE:Rows c.physical 0 c.inverse.layout.rows entry:=by
  rw[c.inverseRows]
  exact UniformConditionalSectorReturn.rows_prefix c.physical 0 c.packing.rows
   (c.packing.rows+4*c.physical.length) s entry ready.banks.1 (by omega)
   (fun q h=>nat q (by omega) (by omega))
 have widthsE:Widths c.physical entry:=by
  intro a ha j
  exact (nat _ (by have:=c.widthsBelow a ha;omega) (by have:=c.widthsMetadata a ha;omega)).trans
   (ready.banks.2.1 a ha j)
 have permutationsE:Permutations c.physical entry:=by
  intro a ha j
  exact (nat _ (by have:=c.permutationsBelow a ha;omega) (by have:=c.permutationsMetadata a ha;omega)).trans
   (ready.banks.2.2 a ha j)
 have inverseWidths:∀a∈c.physical,a.widthsBase+a.geometry.widths.length ≤ c.inverse.layout.suffix:=by
  rw[c.inverseSuffix];exact c.widthsBelow
 have inversePerms:∀a∈c.physical,a.permutationBase+a.geometry.widths.sum ≤ c.inverse.layout.suffix:=by
  rw[c.inverseSuffix];exact c.permutationsBelow
 obtain ⟨mid,z,last,completed,lastRun,lastCheap,zp,values,outZ,rootsZ,natZ,scalarZ⟩:=UniformConditionalSectorReturnRetention.execution
  child c.inverse c.physical c.inverseLength (c.physicalVolume.trans c.inverseVolume) c.loop c.loopVolume
  c.scatter c.scatterB c.scatterVolume c.scatterSource c.scatterBuffer c.scatterDirectory cost (packed c v) x entry
  root tableE pending constants count dir fresh argsE rowsE widthsE permutationsE inverseWidths inversePerms
  c.cacheBelow positive (by rw[c.inverseB];omega) rfl eb
 have lastRun':BoundedExecution (UniformConditionalSectorReturn.programFor child W) n x c.metadata.B entry last z:=by
  simpa only[c.inverseB] using lastRun
 have movedLast:=UniformBoundedAssembly.boundedExecution_placed (UniformConditionalKernelLayout.kernel_code child W)
  (by rw[UniformConditionalSectorReturn.program_length];omega) (by omega) lastRun'
 rw[show placed 372 entry=setPC t 372 by cases t;rfl] at movedLast
 let u:=setPC z (child.length+613)
 have stop:BoundedExecution (programFor child W) n x c.metadata.B u 1 u:=.halt movedLast.final_bound
  (by simp[step,u,setPC,UniformConditionalKernelLayout.halt_at])
 refine ⟨mid,u,first+(last+1),completed,moved.executes (movedLast.executes stop),?_,rfl,values,
  outZ.trans outputs,rootsZ.trans roots,?_,?_⟩
 · change first ≤ movementCost c at cheap
   omega
 · intro q suffix metadata before stack inverse
   exact (natZ q before (by rw[c.inverseSuffix];exact suffix) stack inverse).trans (nat q suffix metadata)
 · intro q packed buffer before native temporary destination
   exact (scalarZ q before buffer native temporary destination).trans (scalar q packed buffer)
end
end ExactFourierCircuits.UniformConditionalKernelRetention

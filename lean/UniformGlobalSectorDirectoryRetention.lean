import UniformGlobalDiagonalChildPrefix
set_option autoImplicit false
/- Physical count and generated-directory supplements. Earlier frozen
results remain unchanged. Every postcondition comes from actual202 and the
subsequent literal loaders, with the same actual218/372/504 programs. -/
namespace ExactFourierCircuits.UniformProducedSectorChildABI
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformSectorPackingMachine (PhysicalAxis)
noncomputable section
theorem execution_directory {W n a i frontier : ℕ}
 (as : List UniformSectorPackingMachine.PhysicalAxis) (L : UniformSectorMetadataMachine.Layout)
 (g : UniformAllSectorTransposeMachine.Geometry W false (states as))
 (v : ℕ → ℕ → Scalar) (x : Fin n → ℂ) (s : State)
 (sameB : g.B=L.B) (sameVolume : g.volume=L.total)
 (hlen : as.length=L.ell) (hvolume : UniformSectorPackingMachine.physicalVolume as=L.total)
 (rows : UniformSectorPackingMachine.Rows as 0 a s) (widths : UniformSectorPackingMachine.Widths as s)
 (below : ∀ ax ∈ as,ax.widthsBase+ax.geometry.widths.length ≤ L.rows)
 (sep : a+4*L.ell ≤ L.rows) (entry : g.directory+5*L.total ≤ L.B)
 (directory : L.directory+3*L.total ≤ g.directory) (code : 218 ≤ L.B) (pc : s.pc=0)
 (count : s.natReg 102+1=L.ell) (ha : s.natReg 3201=a) (hd : s.natReg 3202=L.rows)
 (hs : s.natReg 3213=L.suffix) (ht : s.natReg 3214=L.stack) (hq : s.natReg 3215=L.directory)
 (he : s.natReg 4441=g.directory) (hb : s.natReg 4442=g.buffer)
 (native : s.natReg 4531=g.native) (volume : s.natReg 4530=g.volume)
 (source : UniformAllSectorTransposeMachine.Source g v s)
 (hi : i < (states as).length) (index : s.natReg 5800=i) (fresh : s.natReg 5801=frontier)
 (wb : WordBound L.B s) :
 ∃ u,BoundedExecution (programFor W) n x L.B s
  (UniformSectorMetadataMachine.treeCost
    (UniformSectorMetadataMachine.counts (UniformMultiAxisSectorMetadataPreparation.metadataAxes as))+
   43*L.ell+(12*W+44)*(states as).length+7*W*L.total+66) u ∧ u.pc=217 ∧
 UniformSectorChildEntryPreparation.ChildHeader ((states as)[i]'hi).pairs
  (g.buffer+W*((states as)[i]'hi).start) ((states as)[i]'hi).width frontier u ∧
 u.natReg 4122=2^(u.natReg 4120) ∧
 GroupedSource W (g.buffer+W*((states as)[i]'hi).start) ((states as)[i]'hi).width
  (UniformAllSectorTransposeMachine.slice v ((states as)[i]'hi)) u ∧
 UniformAllSectorTransposeMachine.Filled g v (states as).length u ∧
 UniformAllSectorTransposeMachine.Table g u ∧
 u.natReg 464=(states as).length ∧u.natReg 4441=g.directory ∧u.natReg 5801=frontier ∧
 u.natReg 5807=((states as)[i]'hi).start ∧
 u.natReg 5808=W*((states as)[i]'hi).width ∧
 (∀ q,100 ≤ q → q ≤ 106 → u.natReg q=s.natReg q) ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀ q,q < L.rows → u.natHeap q=s.natHeap q) ∧
 UniformScalarCopyMachine.Outside g.buffer (W*g.volume) s.scalarHeap u := by
 obtain ⟨t,run,tp,filled,table,num,saved,outputs,roots,low,out⟩ :=
  UniformProducedSectorTransposePreparation.execution as L g v x s sameB sameVolume hlen hvolume
   rows widths below sep entry directory (by omega) pc count ha hd hs ht hq he hb native volume source wb
 have link := UniformAssembly.embed_code []
  (UniformProducedSectorTransposePreparation.programFor W) (setup.map Op.code ++ [.halt]) 202
 simp only [List.length_nil] at link
 have moved := UniformBoundedAssembly.boundedExecution_placed link
  (by rw [UniformProducedSectorTransposePreparation.program_length];omega) (by omega) run
 rw [show placed 0 s=s by cases s;simp [placed]] at moved
 let ready := setPC t 202
 have kept := execution_keeps run
 have args : Args i frontier g.directory ready :=
  ⟨(kept 5800 (by simp)).trans index,(kept 5801 (by simp)).trans fresh,
   (kept 4441 (by simp)).trans he⟩
 have cell : UniformSectorBatchDirectoryMachine.BatchCell W g.directory g.buffer i ((states as)[i]'hi) ready :=
  table i hi
 have row : g.directory+5*(i+1) ≤ L.B := by
  have bound := g.entry
  rw [sameB] at bound
  nlinarith
 have safe := setup_safe args cell row (by omega) moved.final_bound
 have second := block_runs setup (programFor W) 202 n L.B x ready (setup_code W) rfl moved.final_bound
  (by rw [setup_length];omega) safe.1 safe.2
 let u := applyBlock setup ready
 have up : u.pc=217 := by rw [applyBlock_pc,setup_length];rfl
 have stop : BoundedExecution (programFor W) n x L.B u 1 u :=
  .halt second.final_bound (by rw [step,up,halt_at])
 have head := setup_header args cell
 have width := UniformSectorBatchDirectoryMachine.sector_width
  (UniformSectorPackingMachine.physicalAxes as) i hi
 have hw : u.natReg 4122=2^(u.natReg 4120) := by
  rw [head.1.width,head.1.exponent]
  exact width
 refine ⟨u,?_,up,head.1,hw,?_,
  filled,table,?_,?_,?_,head.2.1,head.2.2,?_,outputs,roots,low,out⟩
 · convert moved.executes (second.executes stop) using 1
   · rfl
   · simp only [setup_length,states]
 · intro r hr j hj
   exact filled i hi hi r hr j hj
 · exact ((setup_frame ready).2.2.2.2.2 464 (by omega) (by omega)).trans num
 · exact ((setup_frame ready).2.2.2.2.2 4441 (by omega) (by omega)).trans args.directory
 · exact ((setup_frame ready).2.2.2.2.2 5801 (by omega) (by omega)).trans args.frontier
 · intro q hlo hhi
   exact ((setup_frame ready).2.2.2.2.2 q (by omega) (by omega)).trans (saved q hlo hhi)

end
end ExactFourierCircuits.UniformProducedSectorChildABI

namespace ExactFourierCircuits.UniformGlobalPackingChildPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformSectorPackingMachine (PhysicalAxis)
noncomputable section
theorem execution_directory {W n i frontier : ℕ}
 (gp : UniformGlobalRolePackingMachine.Geometry W) (as : List PhysicalAxis)
 (physicalVolume : UniformSectorPackingMachine.physicalVolume as=gp.volume)
 (physicalLength : as.length=gp.ell) (L : UniformSectorMetadataMachine.Layout)
 (gt : UniformAllSectorTransposeMachine.Geometry W false (UniformProducedSectorChildABI.states as))
 (v : ℕ → Fin gp.volume → Scalar) (x : Fin n → ℂ) (s : State)
 (sameB : gp.B=L.B) (sameTransposeB : gt.B=L.B)
 (sameVolume : gp.volume=L.total) (sameTransposeVolume : gt.volume=L.total)
 (native : gt.native=gp.destination) (length : as.length=L.ell)
 (header : UniformGlobalRolePackingMachine.Header gp s)
 (banks : UniformGlobalRolePackingMachine.Banks gp as s)
 (widthsBelow : ∀ a ∈ as,a.widthsBase+a.geometry.widths.length ≤ gp.suffix)
 (permutationsBelow : ∀ a ∈ as,a.permutationBase+a.geometry.widths.sum ≤ gp.suffix)
 (sectorBelow : ∀ a ∈ as,a.widthsBase+a.geometry.widths.length ≤ L.rows)
 (rowsBelow : gp.rows+4*L.ell ≤ L.rows)
 (entry : gt.directory+5*L.total ≤ L.B)
 (directory : L.directory+3*L.total ≤ gt.directory) (code : 372 ≤ L.B)
 (count : s.natReg 102+1=L.ell) (ha : s.natReg 3201=gp.rows) (hd : s.natReg 3202=L.rows)
 (hs : s.natReg 3213=L.suffix) (ht : s.natReg 3214=L.stack) (hq : s.natReg 3215=L.directory)
 (he : s.natReg 4441=gt.directory) (hb : s.natReg 4442=gt.buffer)
 (hn : s.natReg 4531=gt.native) (hv : s.natReg 4530=gt.volume)
 (source : UniformGlobalRolePackingMachine.Source gp v s)
 (hi : i < (UniformProducedSectorChildABI.states as).length)
 (index : s.natReg 5800=i) (fresh : s.natReg 5801=frontier)
 (pc : s.pc=0) (wb : WordBound L.B s) :
 ∃ u ticks,BoundedExecution (programFor W) n x L.B s ticks u ∧
 ticks ≤ W*(213*gp.volume+31)+
  UniformSectorMetadataMachine.treeCost
   (UniformSectorMetadataMachine.counts (UniformMultiAxisSectorMetadataPreparation.metadataAxes as))+
  43*L.ell+(12*W+44)*(UniformProducedSectorChildABI.states as).length+7*W*L.total+73 ∧
 u.pc=371 ∧
 UniformSectorChildEntryPreparation.ChildHeader ((UniformProducedSectorChildABI.states as)[i]'hi).pairs
  (gt.buffer+W*((UniformProducedSectorChildABI.states as)[i]'hi).start)
  ((UniformProducedSectorChildABI.states as)[i]'hi).width frontier u ∧
 u.natReg 4122=2^(u.natReg 4120) ∧
 UniformProducedSectorChildABI.GroupedSource W
  (gt.buffer+W*((UniformProducedSectorChildABI.states as)[i]'hi).start)
  ((UniformProducedSectorChildABI.states as)[i]'hi).width
  (UniformAllSectorTransposeMachine.slice
   (packedValues gp (UniformGlobalRolePackingMachine.permutation gp as physicalVolume) v)
   ((UniformProducedSectorChildABI.states as)[i]'hi)) u ∧
 UniformAllSectorTransposeMachine.Filled gt
  (packedValues gp (UniformGlobalRolePackingMachine.permutation gp as physicalVolume) v)
  (UniformProducedSectorChildABI.states as).length u ∧
 UniformAllSectorTransposeMachine.Table gt u ∧
 u.natReg 464=(UniformProducedSectorChildABI.states as).length ∧
 u.natReg 4441=gt.directory ∧u.natReg 5801=frontier ∧
 (∀ q,100 ≤ q → q ≤ 106 → u.natReg q=s.natReg q) ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀ q,q < gp.destination → q < gt.buffer → u.scalarHeap q=s.scalarHeap q) := by
 have firstBound : WordBound gp.B s := by rw [sameB];exact wb
 obtain ⟨t,ticks,packing,packingCost,tp,packed,frame,nat,out⟩ :=
  UniformGlobalRolePackingMachine.execution gp as physicalVolume physicalLength v x s header banks
   widthsBelow permutationsBelow source pc firstBound
 have packing' : BoundedExecution (UniformGlobalRolePackingMachine.programFor W) n x L.B s ticks t := by
  simpa only [sameB] using packing
 have firstLink := UniformGlobalMovementAssembly.first_code
  (UniformGlobalRolePackingMachine.programFor W) (UniformProducedSectorChildABI.programFor W) []
 simp only [UniformGlobalRolePackingMachine.program_length] at firstLink
 have placedFirst := UniformBoundedAssembly.boundedExecution_placed firstLink
  (by rw [UniformGlobalRolePackingMachine.program_length];omega) (by omega) packing'
 rw [show placed 0 s=s by cases s;simp [placed]] at placedFirst
 let ready := setPC t 0
 have readyBound := changePC_bound L.B t 0 packing'.final_bound (by omega)
 have retained := UniformGlobalRolePackingMachine.banks_transfer gp as physicalLength banks nat widthsBelow permutationsBelow
 have rawSource : UniformAllSectorTransposeMachine.Source gt
  (packedValues gp (UniformGlobalRolePackingMachine.permutation gp as physicalVolume) v) ready :=
  produced_source gp as gt _ v ready native (sameTransposeVolume.trans sameVolume.symm) packed
 have keepsArguments : ∀ q,UniformGlobalRolePackingMachine.Protected q → ready.natReg q=s.natReg q := frame.2.2.1
 have rawCount : ready.natReg 102+1=L.ell := by rw [keepsArguments 102 (by unfold UniformGlobalRolePackingMachine.Protected;omega)];exact count
 have arg3201 : ready.natReg 3201=gp.rows := (keepsArguments 3201 (by unfold UniformGlobalRolePackingMachine.Protected;omega)).trans ha
 have arg3202 : ready.natReg 3202=L.rows := (keepsArguments 3202 (by unfold UniformGlobalRolePackingMachine.Protected;omega)).trans hd
 have arg3213 : ready.natReg 3213=L.suffix := (keepsArguments 3213 (by unfold UniformGlobalRolePackingMachine.Protected;omega)).trans hs
 have arg3214 : ready.natReg 3214=L.stack := (keepsArguments 3214 (by unfold UniformGlobalRolePackingMachine.Protected;omega)).trans ht
 have arg3215 : ready.natReg 3215=L.directory := (keepsArguments 3215 (by unfold UniformGlobalRolePackingMachine.Protected;omega)).trans hq
 have arg4441 : ready.natReg 4441=gt.directory := (keepsArguments 4441 (by unfold UniformGlobalRolePackingMachine.Protected;omega)).trans he
 have arg4442 : ready.natReg 4442=gt.buffer := (keepsArguments 4442 (by unfold UniformGlobalRolePackingMachine.Protected;omega)).trans hb
 have arg4531 : ready.natReg 4531=gt.native := (keepsArguments 4531 (by unfold UniformGlobalRolePackingMachine.Protected;omega)).trans hn
 have arg4530 : ready.natReg 4530=gt.volume := (keepsArguments 4530 (by unfold UniformGlobalRolePackingMachine.Protected;omega)).trans hv
 have arg5800 : ready.natReg 5800=i := (keepsArguments 5800 (by unfold UniformGlobalRolePackingMachine.Protected;omega)).trans index
 have arg5801 : ready.natReg 5801=frontier := (keepsArguments 5801 (by unfold UniformGlobalRolePackingMachine.Protected;omega)).trans fresh
 have realRows : UniformSectorPackingMachine.Rows as 0 gp.rows ready :=
  rows_withPC as 0 gp.rows t 0 retained.1
 have realWidths : UniformSectorPackingMachine.Widths as ready := by
  intro a ha j;exact retained.2.1 a ha j
 obtain ⟨z,second,zp,child,pow,grouped,filled,table,num,directoryKept,freshKept,start,width,saved,outputs,roots,low,scalar⟩ :=
  UniformProducedSectorChildABI.execution_directory as L gt
   (packedValues gp (UniformGlobalRolePackingMachine.permutation gp as physicalVolume) v) x ready
   sameTransposeB sameTransposeVolume length (physicalVolume.trans sameVolume) realRows realWidths sectorBelow rowsBelow
   entry directory (by omega) rfl rawCount arg3201 arg3202 arg3213 arg3214 arg3215 arg4441 arg4442
   arg4531 arg4530 rawSource hi arg5800 arg5801 readyBound
 have secondLink := UniformGlobalMovementAssembly.second_code
  (UniformGlobalRolePackingMachine.programFor W) (UniformProducedSectorChildABI.programFor W) []
 simp only [UniformGlobalRolePackingMachine.program_length,UniformProducedSectorChildABI.program_length,
  show 153+218=371 by rfl] at secondLink
 have placedSecond := UniformBoundedAssembly.boundedExecution_placed secondLink
  (by rw [UniformProducedSectorChildABI.program_length];omega) (by omega) second
 rw [show placed 153 ready=setPC t 153 by cases t;rfl] at placedSecond
 let u := setPC z 371
 have stop : BoundedExecution (programFor W) n x L.B u 1 u :=
  .halt placedSecond.final_bound (by simp [step,u,setPC,halt_at])
 refine ⟨u,ticks+(UniformSectorMetadataMachine.treeCost
   (UniformSectorMetadataMachine.counts (UniformMultiAxisSectorMetadataPreparation.metadataAxes as))+
   43*L.ell+(12*W+44)*(UniformProducedSectorChildABI.states as).length+7*W*L.total+66+1),?_,?_,rfl,
  ⟨child.exponent,child.base,child.width,child.frontier⟩,pow,grouped,filled,table,num,directoryKept,freshKept,?_,
  outputs.trans frame.1,roots.trans frame.2.1,?_⟩
 · convert placedFirst.executes (placedSecond.executes stop) using 1
   rfl
 · omega
 · intro q hlo hhi
   exact (saved q hlo hhi).trans (keepsArguments q (by unfold UniformGlobalRolePackingMachine.Protected;omega))
 · intro q hp hb
   exact (scalar q (Or.inl hb)).trans (out q (Or.inl hp))

end
end ExactFourierCircuits.UniformGlobalPackingChildPreparation

namespace ExactFourierCircuits.UniformGlobalDiagonalChildPrefix
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformSectorPackingMachine (PhysicalAxis)
noncomputable section
theorem execution_directory {W n ordinal frontier:ℕ} (c:Context W) (v:ℕ→ℕ→Scalar) (x:Fin n→ℂ)
 (s:State) (ready:Ready c ordinal frontier v s)
 (hi:ordinal<(UniformProducedSectorChildABI.states c.physical).length)
 (pc:s.pc=0) (wb:WordBound c.metadata.B s):∃u ticks,
 BoundedExecution (programFor W) n x c.metadata.B s ticks u ∧
 ticks≤diagonalTicks c+movementBound c+1 ∧u.pc=503 ∧
 UniformSectorChildEntryPreparation.ChildHeader ((UniformProducedSectorChildABI.states c.physical)[ordinal]'hi).pairs
  (c.transpose.buffer+W*((UniformProducedSectorChildABI.states c.physical)[ordinal]'hi).start)
  ((UniformProducedSectorChildABI.states c.physical)[ordinal]'hi).width frontier u ∧
 u.natReg 4122=2^(u.natReg 4120) ∧
 UniformProducedSectorChildABI.GroupedSource W
  (c.transpose.buffer+W*((UniformProducedSectorChildABI.states c.physical)[ordinal]'hi).start)
  ((UniformProducedSectorChildABI.states c.physical)[ordinal]'hi).width
  (UniformAllSectorTransposeMachine.slice
   (UniformGlobalPackingChildPreparation.packedValues c.packing
    (UniformGlobalRolePackingMachine.permutation c.packing c.physical c.physicalVolume) (phaseValues c v))
   ((UniformProducedSectorChildABI.states c.physical)[ordinal]'hi)) u ∧
 UniformAllSectorTransposeMachine.Filled c.transpose
  (UniformGlobalPackingChildPreparation.packedValues c.packing
   (UniformGlobalRolePackingMachine.permutation c.packing c.physical c.physicalVolume) (phaseValues c v))
  (UniformProducedSectorChildABI.states c.physical).length u ∧
 UniformAllSectorTransposeMachine.Table c.transpose u ∧
 u.natReg 464=(UniformProducedSectorChildABI.states c.physical).length ∧
 u.natReg 4441=c.transpose.directory ∧u.natReg 5801=frontier ∧
 (∀q,100≤q→q≤106→u.natReg q=s.natReg q) ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,q<c.rows.coefficient→q<c.tensor.scalarStack→q<c.tensor.destination→
  q<c.packing.destination→q<c.transpose.buffer→u.scalarHeap q=s.scalarHeap q) := by
 have rowsBound:WordBound c.rows.B s:=by rw[c.sharedB];exact wb
 obtain ⟨t,diagonal,tp,values,saved,outputs,roots,nat,scalars⟩:=
  UniformGlobalTensorDiagonalPreparation.execution c.entries c.rows c.lane c.tensor v x s c.tensorB c.tensorRows
   c.entryLength c.tensorAxes c.entryTotal c.tensorVolume c.tensorPermutation c.tensorCoefficient c.tensorSource
   ready.diagonalHeader ready.directory ready.pools c.poolsBelow ready.tensorHeader ready.source
   (by rw[c.sharedB];have:=c.code;omega) pc rowsBound
 have diagonal':BoundedExecution (UniformGlobalTensorDiagonalPreparation.programFor W) n x c.metadata.B s
  (diagonalTicks c) t:=by simpa only[c.sharedB,diagonalTicks] using diagonal
 have firstLink:=UniformGlobalMovementAssembly.first_code
  (UniformGlobalTensorDiagonalPreparation.programFor W) (UniformGlobalPackingChildPreparation.programFor W) []
 simp only[UniformGlobalTensorDiagonalPreparation.program_length] at firstLink
 have placedFirst:=UniformBoundedAssembly.boundedExecution_placed firstLink
  (by rw[UniformGlobalTensorDiagonalPreparation.program_length];have:=c.code;omega) (by have:=c.code;omega) diagonal'
 rw[show placed 0 s=s by cases s;simp[placed]] at placedFirst
 let entry:=setPC t 0
 have eb:=changePC_bound c.metadata.B t 0 diagonal'.final_bound (by omega)
 have source:UniformGlobalRolePackingMachine.Source c.packing (phaseValues c v) entry:=
  UniformGlobalTensorPackingBridge.packing_source c.packing c.tensor c.entries c.lane c.rows.permutation c.rows.coefficient
   c.volume c.tensorVolume c.tensorOutput v entry values
 have header:=UniformGlobalTensorPackingBridge.packing_header c.packing diagonal' ready.packingHeader
 have newHeader:UniformGlobalRolePackingMachine.Header c.packing entry:=
  ⟨header.volume,header.source,header.destination,header.axes,header.rows,header.suffix,header.stack,header.inverse⟩
 have banks:=UniformGlobalTensorPackingBridge.packing_banks c.packing c.tensor c.rows c.physical s t ready.banks
  c.rowAbove c.permutationAbove c.stackAbove c.widthsLow c.permutationsLow nat
 have newBanks:UniformGlobalRolePackingMachine.Banks c.packing c.physical entry:=by
  refine ⟨UniformGlobalPackingChildPreparation.rows_withPC c.physical 0 c.packing.rows t 0 banks.1,?_,?_⟩
  · intro a member j;exact banks.2.1 a member j
  · intro a member j;exact banks.2.2 a member j
 have kept:=UniformGlobalTensorPackingBridge.execution_keeps diagonal'
 have unchanged (q:ℕ) (member:q∈UniformGlobalTensorPackingBridge.argumentRegisters):entry.natReg q=s.natReg q:=kept q member
 have count:entry.natReg 102+1=c.metadata.ell:=by
  change t.natReg 102+1=c.metadata.ell
  rw[saved 102 (by omega) (by omega)];exact ready.count
 obtain ⟨z,steps,move,cost,zp,child,pow,grouped,filled,table,num,directoryKept,freshKept,retained,zouts,zroots,slow⟩:=
  UniformGlobalPackingChildPreparation.execution_directory c.packing c.physical c.physicalVolume c.physicalLength
   c.metadata c.transpose (phaseValues c v) x entry c.packingB c.transposeB c.metadataVolume c.transposeVolume
   c.packedOutput c.metadataLength newHeader newBanks c.widthsBelow c.permutationsBelow c.sectorBelow
   c.physicalRowsBelow c.batchFit c.directoryBefore (by have:=c.code;omega) count
   ((unchanged 3201 (by simp[UniformGlobalTensorPackingBridge.argumentRegisters])).trans ready.physicalRows)
   ((unchanged 3202 (by simp[UniformGlobalTensorPackingBridge.argumentRegisters])).trans ready.metadataRows)
   ((unchanged 3213 (by simp[UniformGlobalTensorPackingBridge.argumentRegisters])).trans ready.suffix)
   ((unchanged 3214 (by simp[UniformGlobalTensorPackingBridge.argumentRegisters])).trans ready.stack)
   ((unchanged 3215 (by simp[UniformGlobalTensorPackingBridge.argumentRegisters])).trans ready.directoryArg)
   ((unchanged 4441 (by simp[UniformGlobalTensorPackingBridge.argumentRegisters])).trans ready.batchArg)
   ((unchanged 4442 (by simp[UniformGlobalTensorPackingBridge.argumentRegisters])).trans ready.buffer)
   ((unchanged 4531 (by simp[UniformGlobalTensorPackingBridge.argumentRegisters])).trans ready.native)
   ((unchanged 4530 (by simp[UniformGlobalTensorPackingBridge.argumentRegisters])).trans ready.volume)
   source hi ((unchanged 5800 (by simp[UniformGlobalTensorPackingBridge.argumentRegisters])).trans ready.ordinal)
   ((unchanged 5801 (by simp[UniformGlobalTensorPackingBridge.argumentRegisters])).trans ready.frontier) rfl eb
 have secondLink:=UniformGlobalMovementAssembly.second_code
  (UniformGlobalTensorDiagonalPreparation.programFor W) (UniformGlobalPackingChildPreparation.programFor W) []
 simp only[UniformGlobalTensorDiagonalPreparation.program_length,UniformGlobalPackingChildPreparation.program_length,
  show 131+372=503 by rfl] at secondLink
 have placedSecond:=UniformBoundedAssembly.boundedExecution_placed secondLink
  (by rw[UniformGlobalPackingChildPreparation.program_length];have:=c.code;omega) (by have:=c.code;omega) move
 rw[show placed 131 entry=setPC t 131 by cases t;rfl] at placedSecond
 let u:=setPC z 503
 have stop:BoundedExecution (programFor W) n x c.metadata.B u 1 u:=.halt placedSecond.final_bound
  (by simp[step,u,setPC,halt_at])
 refine ⟨u,diagonalTicks c+(steps+1),?_,?_,rfl,⟨child.exponent,child.base,child.width,child.frontier⟩,pow,grouped,filled,table,num,directoryKept,freshKept,?_,
  zouts.trans outputs,zroots.trans roots,?_⟩
 · convert placedFirst.executes (placedSecond.executes stop) using 1
   rfl
 · change steps≤ movementBound c at cost
   omega
 · intro q lo hi
   exact (retained q lo hi).trans (saved q lo hi)

 · intro q coef stack dest packed buffer
   exact (slow q packed buffer).trans (scalars q (Or.inl coef) (Or.inl stack) (Or.inl dest))
end
end ExactFourierCircuits.UniformGlobalDiagonalChildPrefix

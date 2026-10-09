import UniformGlobalTensorPackingBridge
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalDiagonalChildPrefix
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section

def programFor (W:ℕ):Program:=UniformGlobalMovementAssembly.assembly
 (UniformGlobalTensorDiagonalPreparation.programFor W) (UniformGlobalPackingChildPreparation.programFor W) []
lemma program_length (W:ℕ):(programFor W).length=504:=by
 simp only[programFor,UniformGlobalMovementAssembly.assembly_length,UniformGlobalTensorDiagonalPreparation.program_length,
  UniformGlobalPackingChildPreparation.program_length,List.length_nil]
lemma halt_at (W:ℕ):(programFor W)[503]?=some .halt:=by
 have h:=UniformGlobalMovementAssembly.halt_at (UniformGlobalTensorDiagonalPreparation.programFor W)
  (UniformGlobalPackingChildPreparation.programFor W) []
 simpa only[programFor,UniformGlobalTensorDiagonalPreparation.program_length,
  UniformGlobalPackingChildPreparation.program_length,List.length_nil,Nat.add_zero,show 131+372=503 by rfl] using h

/-- Explicit shared banks and ordinary geometry constraints. Every semantic
consumer is an actual literal program; no caller-supplied child action occurs. -/
structure Context (W:ℕ) where
 entries:List UniformGlobalDiagonalRowsMachine.Entry
 physical:List UniformSectorPackingMachine.PhysicalAxis
 lane:Fin 9
 rows:UniformGlobalDiagonalRowsMachine.Layout
 tensor:UniformGlobalTensorDiagonalMachine.Geometry W
 packing:UniformGlobalRolePackingMachine.Geometry W
 metadata:UniformSectorMetadataMachine.Layout
 transpose:UniformAllSectorTransposeMachine.Geometry W false (UniformProducedSectorChildABI.states physical)
 tensorB:tensor.B=rows.B
 packingB:packing.B=metadata.B
 transposeB:transpose.B=metadata.B
 sharedB:rows.B=metadata.B
 tensorRows:tensor.row=rows.rows
 entryLength:entries.length=rows.ell
 tensorAxes:tensor.ell=rows.ell
 entryTotal:UniformGlobalDiagonalRowsMachine.amount entries=rows.total
 tensorVolume:tensor.volume=(entries.map UniformGlobalDiagonalRowsMachine.Entry.radix).prod
 volume:packing.volume=tensor.volume
 metadataVolume:packing.volume=metadata.total
 transposeVolume:transpose.volume=metadata.total
 tensorOutput:packing.source=tensor.destination
 packedOutput:transpose.native=packing.destination
 physicalVolume:UniformSectorPackingMachine.physicalVolume physical=packing.volume
 physicalLength:physical.length=packing.ell
 metadataLength:physical.length=metadata.ell
 tensorPermutation:rows.permutation+rows.total≤tensor.natStack
 tensorCoefficient:rows.coefficient+rows.total≤tensor.scalarStack
 tensorSource:tensor.source+W*tensor.volume≤rows.coefficient ∨rows.coefficient+rows.total≤tensor.source
 poolsBelow:∀a∈entries,a.pool+9*a.radix≤rows.coefficient
 rowAbove:rows.rows+3*rows.ell≤packing.rows
 permutationAbove:rows.permutation+rows.total≤packing.rows
 stackAbove:tensor.natStack+3*tensor.ell≤packing.rows
 widthsLow:∀a∈physical,a.widthsBase+a.geometry.widths.length≤rows.rows ∧
  a.widthsBase+a.geometry.widths.length≤rows.permutation ∧a.widthsBase+a.geometry.widths.length≤tensor.natStack
 permutationsLow:∀a∈physical,a.permutationBase+a.geometry.widths.sum≤rows.rows ∧
  a.permutationBase+a.geometry.widths.sum≤rows.permutation ∧a.permutationBase+a.geometry.widths.sum≤tensor.natStack
 widthsBelow:∀a∈physical,a.widthsBase+a.geometry.widths.length≤packing.suffix
 permutationsBelow:∀a∈physical,a.permutationBase+a.geometry.widths.sum≤packing.suffix
 sectorBelow:∀a∈physical,a.widthsBase+a.geometry.widths.length≤ metadata.rows
 physicalRowsBelow:packing.rows+4*metadata.ell≤ metadata.rows
 batchFit:transpose.directory+5*metadata.total≤ metadata.B
 directoryBefore:metadata.directory+3*metadata.total≤transpose.directory
 code:504≤ metadata.B

structure Ready {W:ℕ} (c:Context W) (ordinal frontier:ℕ) (v:ℕ→ℕ→Scalar) (s:State):Prop where
 diagonalHeader:UniformGlobalDiagonalRowsMachine.Header c.rows c.lane s
 directory:UniformGlobalDiagonalRowsMachine.Directory c.rows.directory c.entries 0 s
 pools:UniformGlobalDiagonalRowsMachine.Pools c.entries s
 tensorHeader:UniformGlobalTensorDiagonalMachine.Header c.tensor s
 source:UniformGlobalTensorDiagonalMachine.Source c.tensor v s
 packingHeader:UniformGlobalRolePackingMachine.Header c.packing s
 banks:UniformGlobalRolePackingMachine.Banks c.packing c.physical s
 count:s.natReg 102+1=c.metadata.ell
 physicalRows:s.natReg 3201=c.packing.rows
 metadataRows:s.natReg 3202=c.metadata.rows
 suffix:s.natReg 3213=c.metadata.suffix
 stack:s.natReg 3214=c.metadata.stack
 directoryArg:s.natReg 3215=c.metadata.directory
 batchArg:s.natReg 4441=c.transpose.directory
 buffer:s.natReg 4442=c.transpose.buffer
 native:s.natReg 4531=c.transpose.native
 volume:s.natReg 4530=c.transpose.volume
 ordinal:s.natReg 5800=ordinal
 frontier:s.natReg 5801=frontier

def diagonalTicks {W:ℕ} (c:Context W):ℕ:=9*c.rows.total+35*c.rows.ell+
 W*(treeCost (c.entries.map UniformGlobalDiagonalRowsMachine.Entry.radix)+20)+14
def movementBound {W:ℕ} (c:Context W):ℕ:=W*(213*c.packing.volume+31)+
 UniformSectorMetadataMachine.treeCost
  (UniformSectorMetadataMachine.counts (UniformMultiAxisSectorMetadataPreparation.metadataAxes c.physical))+
 43*c.metadata.ell+(12*W+44)*(UniformProducedSectorChildABI.states c.physical).length+7*W*c.metadata.total+73

def phaseValues {W:ℕ} (c:Context W) (v:ℕ→ℕ→Scalar):ℕ→Fin c.packing.volume→Scalar:=
 UniformGlobalTensorPackingBridge.outputValues c.packing c.tensor c.entries c.lane c.rows.permutation c.rows.coefficient
  c.volume c.tensorVolume v

/-- One continuous fixed504 prefix performs actual131 diagonal production,
actual all-W153 packing, actual202 gather and15-op generated child argument
reads. Its actual common-C child execution is deliberately the next seam. -/
theorem execution {W n ordinal frontier:ℕ} (c:Context W) (v:ℕ→ℕ→Scalar) (x:Fin n→ℂ)
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
 (∀q,100≤q→q≤106→u.natReg q=s.natReg q) ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders := by
 have rowsBound:WordBound c.rows.B s:=by rw[c.sharedB];exact wb
 obtain ⟨t,diagonal,tp,values,saved,outputs,roots,nat,_scalars⟩:=
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
 obtain ⟨z,steps,move,cost,zp,child,pow,grouped,_filled,_table,retained,zouts,zroots,_slow⟩:=
  UniformGlobalPackingChildPreparation.execution c.packing c.physical c.physicalVolume c.physicalLength
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
 refine ⟨u,diagonalTicks c+(steps+1),?_,?_,rfl,⟨child.exponent,child.base,child.width,child.frontier⟩,pow,grouped,?_,
  zouts.trans outputs,zroots.trans roots⟩
 · convert placedFirst.executes (placedSecond.executes stop) using 1
   rfl
 · change steps≤ movementBound c at cost
   omega
 · intro q lo hi
   exact (retained q lo hi).trans (saved q lo hi)

end
end ExactFourierCircuits.UniformGlobalDiagonalChildPrefix

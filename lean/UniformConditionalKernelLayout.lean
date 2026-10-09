import UniformKernelPreparationRetention
set_option autoImplicit false
namespace ExactFourierCircuits.UniformConditionalKernelLayout
open UniformMachine UniformAssembly
open UniformSectorPackingMachine (PhysicalAxis)
noncomputable section

/-- All fields are ordinary physical bank/size links. No produced source,
cache or recursive transform is hidden in this layout. -/
structure Context (W F reserve:ℕ) where
 packing:UniformGlobalRolePackingMachine.Geometry W
 physical:List PhysicalAxis
 metadata:UniformSectorMetadataMachine.Layout
 gather:UniformAllSectorTransposeMachine.Geometry W false (UniformProducedSectorChildABI.states physical)
 inverse:UniformProducedInversePacking.Preparation W
 loop:UniformConditionalSectorLoop.Geometry W inverse.layout.B F reserve gather.buffer gather.directory
  (UniformProducedSectorChildABI.states physical)
 scatter:UniformAllSectorTransposeMachine.Geometry W true (UniformProducedSectorChildABI.states physical)
 packingB:packing.B=metadata.B
 gatherB:gather.B=metadata.B
 inverseB:inverse.layout.B=metadata.B
 scatterB:scatter.B=inverse.layout.B
 packingVolume:packing.volume=metadata.total
 gatherVolume:gather.volume=metadata.total
 physicalVolume:UniformSectorPackingMachine.physicalVolume physical=packing.volume
 physicalLength:physical.length=packing.ell
 metadataLength:physical.length=metadata.ell
 inverseLength:physical.length=inverse.layout.ell
 inverseVolume:packing.volume=inverse.layout.total
 loopVolume:loop.volume=inverse.layout.total
 scatterVolume:scatter.volume=inverse.layout.total
 gatherSource:gather.native=packing.destination
 scatterSource:scatter.native=inverse.layout.source
 scatterBuffer:scatter.buffer=gather.buffer
 scatterDirectory:scatter.directory=gather.directory
 inverseRows:inverse.layout.rows=packing.rows
 inverseSuffix:inverse.layout.suffix=packing.suffix
 widthsBelow:∀a∈physical,a.widthsBase+a.geometry.widths.length ≤ packing.suffix
 permutationsBelow:∀a∈physical,a.permutationBase+a.geometry.widths.sum ≤ packing.suffix
 widthsMetadata:∀a∈physical,a.widthsBase+a.geometry.widths.length ≤ metadata.rows
 permutationsMetadata:∀a∈physical,a.permutationBase+a.geometry.widths.sum ≤ metadata.rows
 rowsMetadata:packing.rows+4*metadata.ell ≤ metadata.rows
 entry:gather.directory+5*metadata.total ≤ metadata.B
 directory:metadata.directory+3*metadata.total ≤ gather.directory
 cacheBelow:inverse.layout.suffix ≤ F
 scalarLow:3 ≤ packing.destination

structure Ready {W F reserve:ℕ} (c:Context W F reserve) (ordinal:ℕ)
 (v:ℕ → Fin c.packing.volume → Scalar) (s:State):Prop where
 packing:UniformGlobalRolePackingMachine.Header c.packing s
 banks:UniformGlobalRolePackingMachine.Banks c.packing c.physical s
 source:UniformGlobalRolePackingMachine.Source c.packing v s
 count:s.natReg 102+1=c.metadata.ell
 axes:s.natReg 3201=c.packing.rows
 metadataRows:s.natReg 3202=c.metadata.rows
 suffix:s.natReg 3213=c.metadata.suffix
 stack:s.natReg 3214=c.metadata.stack
 directory:s.natReg 3215=c.metadata.directory
 batchDirectory:s.natReg 4441=c.gather.directory
 childBank:s.natReg 4442=c.gather.buffer
 native:s.natReg 4531=c.gather.native
 volume:s.natReg 4530=c.gather.volume
 ordinal:s.natReg 5800=ordinal
 frontier:s.natReg 5801=F
 inverse:UniformGlobalInverseReturn.Args c.inverse c.scatter.directory s
 constants:UniformBinaryCStageMachine.Constants s

def packed {W F reserve:ℕ} (c:Context W F reserve)
 (v:ℕ → Fin c.packing.volume → Scalar):ℕ → ℕ → Scalar:=
 UniformGlobalPackingChildPreparation.packedValues c.packing
  (UniformGlobalRolePackingMachine.permutation c.packing c.physical c.physicalVolume) v

def movementCost {W F reserve:ℕ} (c:Context W F reserve):ℕ:=W*(213*c.packing.volume+31)+
 UniformSectorMetadataMachine.treeCost
  (UniformSectorMetadataMachine.counts (UniformMultiAxisSectorMetadataPreparation.metadataAxes c.physical))+
 43*c.metadata.ell+(12*W+44)*(UniformProducedSectorChildABI.states c.physical).length+7*W*c.metadata.total+73

def programFor (child:Program) (W:ℕ):Program:=UniformGlobalMovementAssembly.assembly
 (UniformGlobalPackingChildPreparation.programFor W) (UniformConditionalSectorReturn.programFor child W) []
lemma program_length (child:Program) (W:ℕ):(programFor child W).length=child.length+614:=by
 simp only[programFor,UniformGlobalMovementAssembly.assembly_length,
  UniformGlobalPackingChildPreparation.program_length,UniformConditionalSectorReturn.program_length,List.length_nil]
 omega
lemma movement_code (child:Program) (W:ℕ):CodeAt (UniformGlobalPackingChildPreparation.programFor W)
 (programFor child W) 0 372:=by
 simpa only[programFor,UniformGlobalPackingChildPreparation.program_length] using
  UniformGlobalMovementAssembly.first_code (UniformGlobalPackingChildPreparation.programFor W)
   (UniformConditionalSectorReturn.programFor child W) []
lemma kernel_code (child:Program) (W:ℕ):CodeAt (UniformConditionalSectorReturn.programFor child W)
 (programFor child W) 372 (child.length+613):=by
 simpa only[programFor,UniformGlobalPackingChildPreparation.program_length,
  UniformConditionalSectorReturn.program_length,show 372+(child.length+241)=child.length+613 by omega] using
  UniformGlobalMovementAssembly.second_code (UniformGlobalPackingChildPreparation.programFor W)
   (UniformConditionalSectorReturn.programFor child W) []
lemma halt_at (child:Program) (W:ℕ):(programFor child W)[child.length+613]?=some .halt:=by
 simpa only[programFor,UniformGlobalPackingChildPreparation.program_length,
  UniformConditionalSectorReturn.program_length,List.length_nil,Nat.add_zero,
  show 372+(child.length+241)=child.length+613 by omega] using
  UniformGlobalMovementAssembly.halt_at (UniformGlobalPackingChildPreparation.programFor W)
   (UniformConditionalSectorReturn.programFor child W) []
end
end ExactFourierCircuits.UniformConditionalKernelLayout

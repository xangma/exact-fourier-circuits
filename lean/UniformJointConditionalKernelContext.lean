import UniformJointConditionalKernelBanks
set_option autoImplicit false
namespace ExactFourierCircuits.UniformJointConditionalKernelContext
open UniformJointAllocation UniformSectorPackingMachine
noncomputable section
attribute [local irreducible] Nat.mul

/-- Integer geometry of the actual printed physical axes, without bank contents. -/
structure PhysicalGeometry (c : Constants) (n : ℕ) (physical : List PhysicalAxis) : Prop where
 volume:physicalVolume physical=UniformInitialPreparation.len n
 length:physical.length=UniformAllAxisSeedPreparation.axisCount n
 widths:∀a∈physical,a.widthsBase+a.geometry.widths.length≤3*slab c n
 permutations:∀a∈physical,a.permutationBase+a.geometry.widths.sum≤3*slab c n

def context (c : Constants) (n : ℕ) (hn : 0<n) (roles : 0<c.roles) (R : ℕ) (reserve : R≤fixed c)
 (physical : List PhysicalAxis) (shape : PhysicalGeometry c n physical) :
 UniformConditionalKernelLayout.Context c.roles (12*slab c n) R where
 packing:=UniformJointConditionalKernelBanks.packing c n hn
 physical:=physical
 metadata:=sectorLayout c n hn
 gather:=transposeGeometry c n hn (physicalAxes physical) shape.volume
 inverse:=UniformJointInversePackingPreparation.preparation c n hn roles
 loop:=UniformJointConditionalKernelBanks.loop c n hn R reserve physical shape.volume
 scatter:=UniformJointConditionalKernelBanks.scatter c n hn physical shape.volume
 packingB:=rfl
 gatherB:=rfl
 inverseB:=rfl
 scatterB:=rfl
 packingVolume:=rfl
 gatherVolume:=rfl
 physicalVolume:=shape.volume
 physicalLength:=shape.length
 metadataLength:=shape.length
 inverseLength:=shape.length
 inverseVolume:=rfl
 loopVolume:=rfl
 scatterVolume:=rfl
 gatherSource:=rfl
 scatterSource:=rfl
 scatterBuffer:=rfl
 scatterDirectory:=rfl
 inverseRows:=rfl
 inverseSuffix:=rfl
 widthsBelow:=by
  intro a ha
  exact (shape.widths a ha).trans (show 3*slab c n≤7*slab c n by omega)
 permutationsBelow:=by
  intro a ha
  exact (shape.permutations a ha).trans (show 3*slab c n≤7*slab c n by omega)
 widthsMetadata:=by
  intro a ha
  exact (shape.widths a ha).trans (show 3*slab c n≤6*slab c n by omega)
 permutationsMetadata:=by
  intro a ha
  exact (shape.permutations a ha).trans (show 3*slab c n≤6*slab c n by omega)
 rowsMetadata:=by
  have h:=actual_arithmetic c n hn
  dsimp only at h
  rw [Nat.mul_assoc 2 c.roles] at h
  change 5*slab c n+4*UniformAllAxisSeedPreparation.axisCount n≤6*slab c n
  omega
 entry:=by
  have h:=actual_arithmetic c n hn
  dsimp only at h
  rw [Nat.mul_assoc 2 c.roles] at h
  change 10*slab c n+5*UniformInitialPreparation.len n≤envelope c n
  unfold envelope;omega
 directory:=by
  have h:=actual_arithmetic c n hn
  dsimp only at h
  rw [Nat.mul_assoc 2 c.roles] at h
  change 9*slab c n+3*UniformInitialPreparation.len n≤10*slab c n
  omega
 cacheBelow:=by change 7*slab c n≤12*slab c n;omega
 scalarLow:=by have:=positive c n;change 3≤5*slab c n;omega

/-- The actual recursive reserve uses the same fixed static tapes. -/
def actualReserveContext (c : Constants) (n : ℕ) (hn : 0<n) (roles : 0<c.roles)
 (physical : List PhysicalAxis) (shape : PhysicalGeometry c n physical) :
 UniformConditionalKernelLayout.Context c.roles (allocate c n).fresh (payload c+5) :=
 context c n hn roles (payload c+5) (UniformJointConditionalKernelBanks.reserve_bound c) physical shape

lemma addresses (c : Constants) (n : ℕ) (hn : 0<n) (roles : 0<c.roles) (R : ℕ) (reserve : R≤fixed c)
 (physical : List PhysicalAxis) (shape : PhysicalGeometry c n physical) :
 let x:=context c n hn roles R reserve physical shape
 x.packing.source=2*slab c n ∧x.packing.destination=5*slab c n ∧
 x.gather.native=5*slab c n ∧x.gather.buffer=6*slab c n ∧x.gather.directory=10*slab c n ∧
 x.inverse.layout.source=7*slab c n ∧x.inverse.layout.destination=8*slab c n ∧x.inverse.destination=2*slab c n ∧
 x.scatter.native=7*slab c n ∧x.scatter.buffer=6*slab c n ∧
 x.packing.rows=5*slab c n ∧x.metadata.rows=6*slab c n ∧x.metadata.directory=9*slab c n ∧
 x.packing.suffix=7*slab c n ∧x.packing.stack=8*slab c n ∧x.packing.inverse=11*slab c n ∧
 x.loop.volume=UniformInitialPreparation.len n := by
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end
end ExactFourierCircuits.UniformJointConditionalKernelContext

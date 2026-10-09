import UniformJointKernelDiagonalFields

set_option autoImplicit false
namespace ExactFourierCircuits.UniformJointDiagonalContext
noncomputable section
open UniformJointAllocation UniformAllAxisSeedPreparation UniformSectorPackingMachine
attribute [local irreducible] Nat.mul
attribute [local irreducible] Nat.add

/-- Every operational K→D cache frame uses the common2U boundary. -/
def links (c : Constants) (n : ℕ) (hn : 0<n) (roles : 0<c.roles)
    (as : List UniformGlobalDiagonalRowsMachine.Entry)
    (selected:as.map UniformGlobalDiagonalRowsMachine.Entry.radix=List.ofFn (UniformSelectedCRT.radices n))
    (pools:∀a∈as,a.pool+9*a.radix≤2*slab c n)
    (physical : List PhysicalAxis) (shape : PhysicalPlacement c n physical)
    (R : ℕ) (bound:R≤fixed c) :
    UniformKernelDiagonalBanks.Links (W:=c.roles) (F:=12*slab c n) (R:=R)
      (UniformJointConditionalKernelContext.context c n hn roles R bound physical shape.shape)
      (context c n hn roles as selected pools physical shape) where
  natEnd:=2*slab c n
  scalarEnd:=2*slab c n
  bound:=field_bound c n hn roles as selected pools physical shape R bound
  volume:=field_volume c n hn roles as selected pools physical shape R bound
  source:=field_source c n hn roles as selected pools physical shape R bound
  lane:=field_lane c n hn roles as selected pools physical shape R bound
  directory:=field_directory c n hn roles as selected pools physical shape R bound
  pools:=field_pools c n hn roles as selected pools physical shape R bound
  natPacking:=field_natPacking c n hn roles as selected pools physical shape R bound
  natMetadata:=field_natMetadata c n hn roles as selected pools physical shape R bound
  natFresh:=field_natFresh c n hn roles as selected pools physical shape R bound
  natStack:=field_natStack c n hn roles as selected pools physical shape R bound
  natInverse:=field_natInverse c n hn roles as selected pools physical shape R bound
  scalarPacked:=field_scalarPacked c n hn roles as selected pools physical shape R bound
  scalarBuffer:=field_scalarBuffer c n hn roles as selected pools physical shape R bound
  scalarFresh:=field_scalarFresh c n hn roles as selected pools physical shape R bound
  scalarNative:=field_scalarNative c n hn roles as selected pools physical shape R bound
  scalarTemporary:=field_scalarTemporary c n hn roles as selected pools physical shape R bound
  scalarFinal:=field_scalarFinal c n hn roles as selected pools physical shape R bound

end
end ExactFourierCircuits.UniformJointDiagonalContext

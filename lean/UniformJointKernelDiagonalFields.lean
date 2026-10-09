import UniformJointDiagonalContextBindings
import UniformKernelDiagonalBanks

set_option autoImplicit false
namespace ExactFourierCircuits.UniformJointDiagonalContext
noncomputable section
open UniformJointAllocation UniformAllAxisSeedPreparation UniformSectorPackingMachine
attribute [local irreducible] Nat.mul
attribute [local irreducible] Nat.add

theorem field_bound (c : Constants) (n : ℕ) (_hn : 0<n) (_roles : 0<c.roles)
    (_as : List UniformGlobalDiagonalRowsMachine.Entry)
    (_selected:_as.map UniformGlobalDiagonalRowsMachine.Entry.radix=List.ofFn (UniformSelectedCRT.radices n))
    (_pools:∀a∈_as,a.pool+9*a.radix≤2*slab c n)
    (_physical : List PhysicalAxis) (_shape : PhysicalPlacement c n _physical)
    (_R : ℕ) (_bound:_R≤fixed c) :
    (context c n _hn _roles _as _selected _pools _physical _shape).metadata.B=(UniformJointConditionalKernelContext.context c n _hn _roles _R _bound _physical _shape.shape).metadata.B := by rfl


theorem field_volume (c : Constants) (n : ℕ) (_hn : 0<n) (_roles : 0<c.roles)
    (_as : List UniformGlobalDiagonalRowsMachine.Entry)
    (_selected:_as.map UniformGlobalDiagonalRowsMachine.Entry.radix=List.ofFn (UniformSelectedCRT.radices n))
    (_pools:∀a∈_as,a.pool+9*a.radix≤2*slab c n)
    (_physical : List PhysicalAxis) (_shape : PhysicalPlacement c n _physical)
    (_R : ℕ) (_bound:_R≤fixed c) :
    (UniformJointConditionalKernelContext.context c n _hn _roles _R _bound _physical _shape.shape).packing.volume=(context c n _hn _roles _as _selected _pools _physical _shape).packing.volume := by
  exact ((same_kernel c n _hn _roles _as _selected _pools _physical _shape _R _bound).2.2.1).symm.trans
    (context c n _hn _roles _as _selected _pools _physical _shape).volume.symm


theorem field_source (c : Constants) (n : ℕ) (_hn : 0<n) (_roles : 0<c.roles)
    (_as : List UniformGlobalDiagonalRowsMachine.Entry)
    (_selected:_as.map UniformGlobalDiagonalRowsMachine.Entry.radix=List.ofFn (UniformSelectedCRT.radices n))
    (_pools:∀a∈_as,a.pool+9*a.radix≤2*slab c n)
    (_physical : List PhysicalAxis) (_shape : PhysicalPlacement c n _physical)
    (_R : ℕ) (_bound:_R≤fixed c) :
    (UniformJointConditionalKernelContext.context c n _hn _roles _R _bound _physical _shape.shape).inverse.destination=(context c n _hn _roles _as _selected _pools _physical _shape).tensor.source := by rfl


theorem field_lane (c : Constants) (n : ℕ) (_hn : 0<n) (_roles : 0<c.roles)
    (_as : List UniformGlobalDiagonalRowsMachine.Entry)
    (_selected:_as.map UniformGlobalDiagonalRowsMachine.Entry.radix=List.ofFn (UniformSelectedCRT.radices n))
    (_pools:∀a∈_as,a.pool+9*a.radix≤2*slab c n)
    (_physical : List PhysicalAxis) (_shape : PhysicalPlacement c n _physical)
    (_R : ℕ) (_bound:_R≤fixed c) :
    (context c n _hn _roles _as _selected _pools _physical _shape).lane=0 := by rfl


theorem field_directory (c : Constants) (n : ℕ) (_hn : 0<n) (_roles : 0<c.roles)
    (_as : List UniformGlobalDiagonalRowsMachine.Entry)
    (_selected:_as.map UniformGlobalDiagonalRowsMachine.Entry.radix=List.ofFn (UniformSelectedCRT.radices n))
    (_pools:∀a∈_as,a.pool+9*a.radix≤2*slab c n)
    (_physical : List PhysicalAxis) (_shape : PhysicalPlacement c n _physical)
    (_R : ℕ) (_bound:_R≤fixed c) :
    (context c n _hn _roles _as _selected _pools _physical _shape).rows.directory+2*(context c n _hn _roles _as _selected _pools _physical _shape).entries.length≤2*slab c n := by
    have len:_as.length=axisCount n:=by
      have h:=congrArg List.length _selected
      simpa only [List.length_map,List.length_ofFn] using h
    have h:=actual_arithmetic c n _hn
    dsimp only at h
    rw [Nat.mul_assoc 2 c.roles] at h
    change slab c n+2*_as.length≤2*slab c n
    rw [len]
    omega


theorem field_pools (c : Constants) (n : ℕ) (_hn : 0<n) (_roles : 0<c.roles)
    (_as : List UniformGlobalDiagonalRowsMachine.Entry)
    (_selected:_as.map UniformGlobalDiagonalRowsMachine.Entry.radix=List.ofFn (UniformSelectedCRT.radices n))
    (_pools:∀a∈_as,a.pool+9*a.radix≤2*slab c n)
    (_physical : List PhysicalAxis) (_shape : PhysicalPlacement c n _physical)
    (_R : ℕ) (_bound:_R≤fixed c) :
    ∀a∈(context c n _hn _roles _as _selected _pools _physical _shape).entries,a.pool+9*a.radix≤2*slab c n := by exact _pools


theorem field_natPacking (c : Constants) (n : ℕ) (_hn : 0<n) (_roles : 0<c.roles)
    (_as : List UniformGlobalDiagonalRowsMachine.Entry)
    (_selected:_as.map UniformGlobalDiagonalRowsMachine.Entry.radix=List.ofFn (UniformSelectedCRT.radices n))
    (_pools:∀a∈_as,a.pool+9*a.radix≤2*slab c n)
    (_physical : List PhysicalAxis) (_shape : PhysicalPlacement c n _physical)
    (_R : ℕ) (_bound:_R≤fixed c) :
    2*slab c n≤(UniformJointConditionalKernelContext.context c n _hn _roles _R _bound _physical _shape.shape).packing.suffix := by change 2*slab c n≤7*slab c n;omega


theorem field_natMetadata (c : Constants) (n : ℕ) (_hn : 0<n) (_roles : 0<c.roles)
    (_as : List UniformGlobalDiagonalRowsMachine.Entry)
    (_selected:_as.map UniformGlobalDiagonalRowsMachine.Entry.radix=List.ofFn (UniformSelectedCRT.radices n))
    (_pools:∀a∈_as,a.pool+9*a.radix≤2*slab c n)
    (_physical : List PhysicalAxis) (_shape : PhysicalPlacement c n _physical)
    (_R : ℕ) (_bound:_R≤fixed c) :
    2*slab c n≤(UniformJointConditionalKernelContext.context c n _hn _roles _R _bound _physical _shape.shape).metadata.rows := by change 2*slab c n≤6*slab c n;omega


theorem field_natFresh (c : Constants) (n : ℕ) (_hn : 0<n) (_roles : 0<c.roles)
    (_as : List UniformGlobalDiagonalRowsMachine.Entry)
    (_selected:_as.map UniformGlobalDiagonalRowsMachine.Entry.radix=List.ofFn (UniformSelectedCRT.radices n))
    (_pools:∀a∈_as,a.pool+9*a.radix≤2*slab c n)
    (_physical : List PhysicalAxis) (_shape : PhysicalPlacement c n _physical)
    (_R : ℕ) (_bound:_R≤fixed c) :
    2*slab c n≤12*slab c n := by omega


theorem field_natStack (c : Constants) (n : ℕ) (_hn : 0<n) (_roles : 0<c.roles)
    (_as : List UniformGlobalDiagonalRowsMachine.Entry)
    (_selected:_as.map UniformGlobalDiagonalRowsMachine.Entry.radix=List.ofFn (UniformSelectedCRT.radices n))
    (_pools:∀a∈_as,a.pool+9*a.radix≤2*slab c n)
    (_physical : List PhysicalAxis) (_shape : PhysicalPlacement c n _physical)
    (_R : ℕ) (_bound:_R≤fixed c) :
    2*slab c n≤(UniformJointConditionalKernelContext.context c n _hn _roles _R _bound _physical _shape.shape).inverse.layout.stack := by change 2*slab c n≤8*slab c n;omega


theorem field_natInverse (c : Constants) (n : ℕ) (_hn : 0<n) (_roles : 0<c.roles)
    (_as : List UniformGlobalDiagonalRowsMachine.Entry)
    (_selected:_as.map UniformGlobalDiagonalRowsMachine.Entry.radix=List.ofFn (UniformSelectedCRT.radices n))
    (_pools:∀a∈_as,a.pool+9*a.radix≤2*slab c n)
    (_physical : List PhysicalAxis) (_shape : PhysicalPlacement c n _physical)
    (_R : ℕ) (_bound:_R≤fixed c) :
    2*slab c n≤(UniformJointConditionalKernelContext.context c n _hn _roles _R _bound _physical _shape.shape).inverse.layout.inverse := by change 2*slab c n≤11*slab c n;omega


theorem field_scalarPacked (c : Constants) (n : ℕ) (_hn : 0<n) (_roles : 0<c.roles)
    (_as : List UniformGlobalDiagonalRowsMachine.Entry)
    (_selected:_as.map UniformGlobalDiagonalRowsMachine.Entry.radix=List.ofFn (UniformSelectedCRT.radices n))
    (_pools:∀a∈_as,a.pool+9*a.radix≤2*slab c n)
    (_physical : List PhysicalAxis) (_shape : PhysicalPlacement c n _physical)
    (_R : ℕ) (_bound:_R≤fixed c) :
    2*slab c n≤(UniformJointConditionalKernelContext.context c n _hn _roles _R _bound _physical _shape.shape).packing.destination := by change 2*slab c n≤5*slab c n;omega


theorem field_scalarBuffer (c : Constants) (n : ℕ) (_hn : 0<n) (_roles : 0<c.roles)
    (_as : List UniformGlobalDiagonalRowsMachine.Entry)
    (_selected:_as.map UniformGlobalDiagonalRowsMachine.Entry.radix=List.ofFn (UniformSelectedCRT.radices n))
    (_pools:∀a∈_as,a.pool+9*a.radix≤2*slab c n)
    (_physical : List PhysicalAxis) (_shape : PhysicalPlacement c n _physical)
    (_R : ℕ) (_bound:_R≤fixed c) :
    2*slab c n≤(UniformJointConditionalKernelContext.context c n _hn _roles _R _bound _physical _shape.shape).gather.buffer := by change 2*slab c n≤6*slab c n;omega


theorem field_scalarFresh (c : Constants) (n : ℕ) (_hn : 0<n) (_roles : 0<c.roles)
    (_as : List UniformGlobalDiagonalRowsMachine.Entry)
    (_selected:_as.map UniformGlobalDiagonalRowsMachine.Entry.radix=List.ofFn (UniformSelectedCRT.radices n))
    (_pools:∀a∈_as,a.pool+9*a.radix≤2*slab c n)
    (_physical : List PhysicalAxis) (_shape : PhysicalPlacement c n _physical)
    (_R : ℕ) (_bound:_R≤fixed c) :
    2*slab c n≤12*slab c n := by omega


theorem field_scalarNative (c : Constants) (n : ℕ) (_hn : 0<n) (_roles : 0<c.roles)
    (_as : List UniformGlobalDiagonalRowsMachine.Entry)
    (_selected:_as.map UniformGlobalDiagonalRowsMachine.Entry.radix=List.ofFn (UniformSelectedCRT.radices n))
    (_pools:∀a∈_as,a.pool+9*a.radix≤2*slab c n)
    (_physical : List PhysicalAxis) (_shape : PhysicalPlacement c n _physical)
    (_R : ℕ) (_bound:_R≤fixed c) :
    2*slab c n≤(UniformJointConditionalKernelContext.context c n _hn _roles _R _bound _physical _shape.shape).scatter.native := by change 2*slab c n≤7*slab c n;omega


theorem field_scalarTemporary (c : Constants) (n : ℕ) (_hn : 0<n) (_roles : 0<c.roles)
    (_as : List UniformGlobalDiagonalRowsMachine.Entry)
    (_selected:_as.map UniformGlobalDiagonalRowsMachine.Entry.radix=List.ofFn (UniformSelectedCRT.radices n))
    (_pools:∀a∈_as,a.pool+9*a.radix≤2*slab c n)
    (_physical : List PhysicalAxis) (_shape : PhysicalPlacement c n _physical)
    (_R : ℕ) (_bound:_R≤fixed c) :
    2*slab c n≤(UniformJointConditionalKernelContext.context c n _hn _roles _R _bound _physical _shape.shape).inverse.layout.destination := by change 2*slab c n≤8*slab c n;omega


theorem field_scalarFinal (c : Constants) (n : ℕ) (_hn : 0<n) (_roles : 0<c.roles)
    (_as : List UniformGlobalDiagonalRowsMachine.Entry)
    (_selected:_as.map UniformGlobalDiagonalRowsMachine.Entry.radix=List.ofFn (UniformSelectedCRT.radices n))
    (_pools:∀a∈_as,a.pool+9*a.radix≤2*slab c n)
    (_physical : List PhysicalAxis) (_shape : PhysicalPlacement c n _physical)
    (_R : ℕ) (_bound:_R≤fixed c) :
    2*slab c n≤(UniformJointConditionalKernelContext.context c n _hn _roles _R _bound _physical _shape.shape).inverse.destination := by change 2*slab c n≤2*slab c n; exact Nat.le_refl _


end
end ExactFourierCircuits.UniformJointDiagonalContext

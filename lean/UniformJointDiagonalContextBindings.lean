import UniformJointDiagonalContext

set_option autoImplicit false
namespace ExactFourierCircuits.UniformJointDiagonalContext
noncomputable section
open UniformJointAllocation UniformAllAxisSeedPreparation UniformSectorPackingMachine

def canonical (c : Constants) (n : ℕ) (hn : 0<n) (roles : 0<c.roles)
    (pool : Fin (axisCount n)→ℕ)
    (value : ∀i : Fin (axisCount n),Fin 9→Fin (radix n i)→ℂ)
    (fit:∀i,pool i+9*radix n i≤2*slab c n)
    (physical : List PhysicalAxis) (shape : PhysicalPlacement c n physical) :
    UniformGlobalDiagonalChildPrefix.Context c.roles :=
  context c n hn roles (entries n pool value) (entries_radices n pool value)
    (by
      intro a ha
      obtain ⟨i,rfl⟩:=List.mem_ofFn.mp ha
      exact fit i) physical shape

theorem PhysicalPlacement.shape {c : Constants} {n : ℕ} {physical : List PhysicalAxis}
    (p : PhysicalPlacement c n physical) :
    UniformJointConditionalKernelContext.PhysicalGeometry c n physical where
  volume:=p.volume
  length:=p.length
  widths:=by intro a ha;exact (p.widths a ha).trans (by omega)
  permutations:=by intro a ha;exact (p.permutations a ha).trans (by omega)

/-- The operational K→D join uses these exact common allocation projections. -/
theorem addresses (c : Constants) (n : ℕ) (hn : 0<n) (roles : 0<c.roles)
    (as : List UniformGlobalDiagonalRowsMachine.Entry)
    (selected:as.map UniformGlobalDiagonalRowsMachine.Entry.radix=List.ofFn (UniformSelectedCRT.radices n))
    (pools:∀a∈as,a.pool+9*a.radix≤2*slab c n)
    (physical : List PhysicalAxis) (shape : PhysicalPlacement c n physical) :
    let d:=context c n hn roles as selected pools physical shape
    d.rows=UniformJointDiagonalHeaderInstallation.rows c n hn ∧
    d.tensor=tensorGeometry c n hn roles ∧
    d.tensor.source=2*slab c n ∧d.tensor.destination=4*slab c n ∧
    d.rows.coefficient=2*slab c n+c.roles*UniformInitialPreparation.len n ∧
    d.rows.rows=2*slab c n ∧d.rows.permutation=3*slab c n ∧
    d.tensor.natStack=4*slab c n ∧d.tensor.scalarStack=3*slab c n ∧
    d.packing.source=4*slab c n ∧d.packing.destination=5*slab c n ∧
    d.packing.rows=5*slab c n ∧d.physical=physical ∧d.tensor.B=envelope c n := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem same_kernel (c : Constants) (n : ℕ) (hn : 0<n) (roles : 0<c.roles)
    (as : List UniformGlobalDiagonalRowsMachine.Entry)
    (selected:as.map UniformGlobalDiagonalRowsMachine.Entry.radix=List.ofFn (UniformSelectedCRT.radices n))
    (pools:∀a∈as,a.pool+9*a.radix≤2*slab c n)
    (physical : List PhysicalAxis) (shape : PhysicalPlacement c n physical)
    (R : ℕ) (bound:R≤fixed c) :
    let d:=context c n hn roles as selected pools physical shape
    let k:=UniformJointConditionalKernelContext.context c n hn roles R bound physical shape.shape
    d.physical=k.physical ∧d.tensor.B=k.packing.B ∧
    d.tensor.volume=k.packing.volume ∧d.tensor.source=k.inverse.destination := by
  exact ⟨rfl,rfl,rfl,rfl⟩

end
end ExactFourierCircuits.UniformJointDiagonalContext

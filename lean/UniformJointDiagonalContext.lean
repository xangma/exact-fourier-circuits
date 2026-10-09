import UniformGlobalDiagonalChildPrefix
import UniformJointDiagonalHeaderInstallation
import UniformJointConditionalKernelContext

set_option autoImplicit false
namespace ExactFourierCircuits.UniformJointDiagonalContext
noncomputable section
open UniformJointAllocation UniformAllAxisSeedPreparation UniformSectorPackingMachine
attribute [local irreducible] Nat.mul

/-- Ordinary addresses of the actual per-axis printed matching banks. -/
structure PhysicalPlacement (c : Constants) (n : ℕ) (physical : List PhysicalAxis) : Prop where
  volume:physicalVolume physical=UniformInitialPreparation.len n
  length:physical.length=axisCount n
  widths:∀a∈physical,a.widthsBase+a.geometry.widths.length≤2*slab c n
  permutations:∀a∈physical,a.permutationBase+a.geometry.widths.sum≤2*slab c n

def entries (n : ℕ) (pool : Fin (axisCount n)→ℕ)
    (value : ∀i : Fin (axisCount n),Fin 9→Fin (radix n i)→ℂ) :
    List UniformGlobalDiagonalRowsMachine.Entry :=
  List.ofFn (fun i=>⟨radix n i,UniformSelectedCRT.radix_pos n i,pool i,value i⟩)

theorem entries_radices (n : ℕ) (pool : Fin (axisCount n)→ℕ)
    (value : ∀i : Fin (axisCount n),Fin 9→Fin (radix n i)→ℂ) :
    (entries n pool value).map UniformGlobalDiagonalRowsMachine.Entry.radix=
      List.ofFn (UniformSelectedCRT.radices n) := by
  simp only [entries,List.map_ofFn]
  rfl

theorem selected_total (n : ℕ) :
    (List.ofFn (UniformSelectedCRT.radices n)).sum=prefixSum n (axisCount n) := by
  rw [List.sum_ofFn]
  calc
    (∑i,UniformSelectedCRT.radices n i)=∑i:Fin (axisCount n),radixAt n i.val := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (radixAt_eq n i).symm
    _=prefixSum n (axisCount n) := by
      exact Fin.sum_univ_eq_sum_range (radixAt n) (axisCount n)

/-- No pool contents, executable action, or desired output is a premise. -/
def context (c : Constants) (n : ℕ) (hn : 0<n) (roles : 0<c.roles)
    (as : List UniformGlobalDiagonalRowsMachine.Entry)
    (selected:as.map UniformGlobalDiagonalRowsMachine.Entry.radix=List.ofFn (UniformSelectedCRT.radices n))
    (pools:∀a∈as,a.pool+9*a.radix≤2*slab c n)
    (physical : List PhysicalAxis) (shape : PhysicalPlacement c n physical) :
    UniformGlobalDiagonalChildPrefix.Context c.roles where
  entries:=as
  physical:=physical
  lane:=0
  rows:=UniformJointDiagonalHeaderInstallation.rows c n hn
  tensor:=tensorGeometry c n hn roles
  packing:=packingGeometry c n hn
  metadata:=sectorLayout c n hn
  transpose:=transposeGeometry c n hn (physicalAxes physical) shape.volume
  tensorB:=rfl
  packingB:=rfl
  transposeB:=rfl
  sharedB:=rfl
  tensorRows:=rfl
  entryLength:=by
    change as.length=axisCount n
    have h:=congrArg List.length selected
    simpa only [List.length_map,List.length_ofFn] using h
  tensorAxes:=rfl
  entryTotal:=by
    change (as.map UniformGlobalDiagonalRowsMachine.Entry.radix).sum=prefixSum n (axisCount n)
    rw [selected,selected_total]
  tensorVolume:=by
    change UniformInitialPreparation.len n=(as.map UniformGlobalDiagonalRowsMachine.Entry.radix).prod
    rw [selected,List.prod_ofFn,UniformSelectedCRT.radices_product]
  volume:=rfl
  metadataVolume:=rfl
  transposeVolume:=rfl
  tensorOutput:=rfl
  packedOutput:=rfl
  physicalVolume:=shape.volume
  physicalLength:=shape.length
  metadataLength:=shape.length
  tensorPermutation:=by
    have h:=actual_arithmetic c n hn
    dsimp only at h
    rw [Nat.mul_assoc 2 c.roles] at h
    change 3*slab c n+prefixSum n (axisCount n)≤4*slab c n
    omega
  tensorCoefficient:=UniformJointDiagonalHeaderInstallation.coefficient_fit c hn roles
  tensorSource:=Or.inl (UniformJointDiagonalHeaderInstallation.source_disjoint c hn roles).le
  poolsBelow:=by
    intro a ha
    exact UniformJointDiagonalHeaderInstallation.pools_before c hn _ (pools a ha)
  rowAbove:=by
    have h:=actual_arithmetic c n hn
    dsimp only at h
    rw [Nat.mul_assoc 2 c.roles] at h
    change 2*slab c n+3*axisCount n≤5*slab c n
    omega
  permutationAbove:=by
    have h:=actual_arithmetic c n hn
    dsimp only at h
    rw [Nat.mul_assoc 2 c.roles] at h
    change 3*slab c n+prefixSum n (axisCount n)≤5*slab c n
    omega
  stackAbove:=by
    have h:=actual_arithmetic c n hn
    dsimp only at h
    rw [Nat.mul_assoc 2 c.roles] at h
    change 4*slab c n+3*axisCount n≤5*slab c n
    omega
  widthsLow:=by
    intro a ha
    have h:=shape.widths a ha
    change _≤2*slab c n ∧_≤3*slab c n ∧_≤4*slab c n
    exact ⟨h,by omega,by omega⟩
  permutationsLow:=by
    intro a ha
    have h:=shape.permutations a ha
    change _≤2*slab c n ∧_≤3*slab c n ∧_≤4*slab c n
    exact ⟨h,by omega,by omega⟩
  widthsBelow:=by
    intro a ha
    have h:=shape.widths a ha
    change _≤7*slab c n
    omega
  permutationsBelow:=by
    intro a ha
    have h:=shape.permutations a ha
    change _≤7*slab c n
    omega
  sectorBelow:=by
    intro a ha
    have h:=shape.widths a ha
    change _≤6*slab c n
    omega
  physicalRowsBelow:=by
    have h:=actual_arithmetic c n hn
    dsimp only at h
    rw [Nat.mul_assoc 2 c.roles] at h
    change 5*slab c n+4*axisCount n≤6*slab c n
    omega
  batchFit:=by
    have h:=actual_arithmetic c n hn
    dsimp only at h
    rw [Nat.mul_assoc 2 c.roles] at h
    change 10*slab c n+5*UniformInitialPreparation.len n≤envelope c n
    unfold envelope
    omega
  directoryBefore:=by
    have h:=actual_arithmetic c n hn
    dsimp only at h
    rw [Nat.mul_assoc 2 c.roles] at h
    change 9*slab c n+3*UniformInitialPreparation.len n≤10*slab c n
    omega
  code:=by
    have h:=fixed_large c
    change 504≤envelope c n
    unfold envelope
    omega

end
end ExactFourierCircuits.UniformJointDiagonalContext

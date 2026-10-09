import UniformJointInversePackingPreparation
import UniformConditionalKernelLayout
set_option autoImplicit false
namespace ExactFourierCircuits.UniformJointConditionalKernelBanks
open UniformJointAllocation UniformSectorPackingMachine
noncomputable section
attribute [local irreducible] Nat.mul

/-- The next movement packs the physically restored2U bank. -/
def packing (c : Constants) (n : ℕ) (hn : 0<n) : UniformGlobalRolePackingMachine.Geometry c.roles :=
 {packingGeometry c n hn with
  source:=2*slab c n
  sourceBelow:=by
   have h:=UniformJointInverseBanks.roles_volume c n hn
   change 2*slab c n+c.roles*UniformInitialPreparation.len n≤5*slab c n
   omega}

/-- True transpose consumes the grouped6U bank and writes7U. -/
def scatter (c : Constants) (n : ℕ) (hn : 0<n) (physical : List PhysicalAxis)
 (volume : physicalVolume physical=UniformInitialPreparation.len n) :
 UniformAllSectorTransposeMachine.Geometry c.roles true (UniformProducedSectorChildABI.states physical) :=
 let g:=transposeGeometry c n hn (physicalAxes physical) volume
 {g with
  native:=7*slab c n
  nativeFit:=by
   have h:=UniformJointInverseBanks.roles_volume c n hn
   change 7*slab c n+c.roles*UniformInitialPreparation.len n≤envelope c n
   unfold envelope;omega
  separation:=by
   have h:=UniformJointInverseBanks.roles_volume c n hn
   change 6*slab c n+c.roles*UniformInitialPreparation.len n≤7*slab c n
   omega}

private lemma room_size (C n q V R : ℕ) (hv : V≤4*n) (hq : q≤V) (hr : R≤C) :
 34*(q+1)+R*(q+1)*V≤100000*(C+1)*(n+2)^2 := by
 have vv:(q+1)*V≤20*(n+2)^2:=by nlinarith only [hv,hq]
 have qq:34*(q+1)≤170*(n+2)^2:=by nlinarith only [hv,hq]
 have mul:R*((q+1)*V)≤C*(20*(n+2)^2):=Nat.mul_le_mul hr vv
 have coeff:170+20*C≤100000*(C+1):=by omega
 have out:=Nat.mul_le_mul_right ((n+2)^2) coeff
 nlinarith only [qq,mul,out]

lemma room (c : Constants) {n : ℕ} (hn : 0<n) (q R : ℕ)
 (volume : 2^q≤UniformInitialPreparation.len n) (reserve : R≤fixed c) :
 12*slab c n+34*(q+1)+R*(q+1)*2^q≤envelope c n := by
 have qV:q≤UniformInitialPreparation.len n:=
  (UniformRecursiveBatchHeaderMachine.index_le_power q).trans volume
 have v:UniformInitialPreparation.len n≤4*n:=(actual_sizes n hn).2.1
 have mul:=Nat.mul_le_mul_left (R*(q+1)) volume
 have size:=room_size (fixed c) n q (UniformInitialPreparation.len n) R v qV reserve
 have polynomial:100000*(fixed c+1)*(n+2)^2≤ slab c n:=Nat.mul_le_mul_left _
  (Nat.pow_le_pow_right (by omega:1≤n+2) (by decide:2≤19))
 unfold envelope
 omega

/-- Every child side condition follows from the actual sector partition. -/
def loop (c : Constants) (n : ℕ) (hn : 0<n) (R : ℕ) (reserve : R≤fixed c)
 (physical : List PhysicalAxis) (volume : (UniformSectorPacking.radices (physicalAxes physical)).prod=UniformInitialPreparation.len n) :
 UniformConditionalSectorLoop.Geometry c.roles (envelope c n) (12*slab c n) R
  (6*slab c n) (10*slab c n) (UniformProducedSectorChildABI.states physical) where
 volume:=UniformInitialPreparation.len n
 fits:=by simpa only [UniformAllSectorPaddingMachine.Fits,UniformProducedSectorChildABI.states,volume] using UniformSectorBatchDirectoryMachine.sector_fits (physicalAxes physical)
 ordered:=UniformSectorBatchDirectoryMachine.sector_before (physicalAxes physical)
 pow:=UniformSectorBatchDirectoryMachine.sector_width (physicalAxes physical)
 low:=by have:=positive c n;omega
 bank:=by have:=UniformJointInverseBanks.roles_volume c n hn;omega
 directory:=by
  have count:=sector_count_le_volume (physicalAxes physical)
  rw [volume] at count
  change (UniformProducedSectorChildABI.states physical).length≤UniformInitialPreparation.len n at count
  have h:=actual_arithmetic c n hn
  dsimp only at h
  rw [Nat.mul_assoc 2 c.roles] at h
  omega
 frontier:=by unfold envelope;omega
 room:=by
  intro i hi
  have fit:=UniformSectorBatchDirectoryMachine.sector_fits (physicalAxes physical) i hi
  have width:=UniformSectorBatchDirectoryMachine.sector_width (physicalAxes physical) i hi
  rw [volume,width] at fit
  change ((UniformProducedSectorChildABI.states physical)[i]'hi).start+
   2^((UniformProducedSectorChildABI.states physical)[i]'hi).pairs≤UniformInitialPreparation.len n at fit
  exact room c hn _ R (by omega) reserve
 square:=by
  intro i hi
  have fit:=UniformSectorBatchDirectoryMachine.sector_fits (physicalAxes physical) i hi
  have width:=UniformSectorBatchDirectoryMachine.sector_width (physicalAxes physical) i hi
  rw [volume,width] at fit
  change ((UniformProducedSectorChildABI.states physical)[i]'hi).start+
   2^((UniformProducedSectorChildABI.states physical)[i]'hi).pairs≤UniformInitialPreparation.len n at fit
  have bound:2^((UniformProducedSectorChildABI.states physical)[i]'hi).pairs≤UniformInitialPreparation.len n:=by omega
  have squares:=Nat.pow_le_pow_left bound 2
  have h:=actual_arithmetic c n hn
  dsimp only at h
  rw [Nat.mul_assoc 2 c.roles] at h
  unfold envelope
  omega
 qBound:=by
  intro i hi
  have fit:=UniformSectorBatchDirectoryMachine.sector_fits (physicalAxes physical) i hi
  have width:=UniformSectorBatchDirectoryMachine.sector_width (physicalAxes physical) i hi
  rw [volume,width] at fit
  change ((UniformProducedSectorChildABI.states physical)[i]'hi).start+
   2^((UniformProducedSectorChildABI.states physical)[i]'hi).pairs≤UniformInitialPreparation.len n at fit
  have index:=UniformRecursiveBatchHeaderMachine.index_le_power ((UniformProducedSectorChildABI.states physical)[i]'hi).pairs
  have h:=actual_arithmetic c n hn
  dsimp only at h
  rw [Nat.mul_assoc 2 c.roles] at h
  unfold envelope
  omega
 widthBound:=by
  intro i hi
  have fit:=UniformSectorBatchDirectoryMachine.sector_fits (physicalAxes physical) i hi
  rw [volume] at fit
  change ((UniformProducedSectorChildABI.states physical)[i]'hi).start+
   ((UniformProducedSectorChildABI.states physical)[i]'hi).width≤UniformInitialPreparation.len n at fit
  have h:=actual_arithmetic c n hn
  dsimp only at h
  rw [Nat.mul_assoc 2 c.roles] at h
  unfold envelope
  omega

lemma reserve_bound (c : Constants) : payload c+5≤fixed c := by unfold fixed;omega
end
end ExactFourierCircuits.UniformJointConditionalKernelBanks

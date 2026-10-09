import UniformActualSectorCost

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualKernelCost
open UniformActualSectorCost UniformConditionalKernelLayout
noncomputable section

/-- Exact nonrecursive terms in the initialized647-instruction kernel proof. -/
def overhead {W F reserve : ℕ} (g : Context W F reserve) : ℕ:=
 movementCost g+213*g.inverse.layout.total+W*(16*g.inverse.layout.total+12)+
 (12*W+20)*(UniformProducedSectorChildABI.states g.physical).length+90

def kernelTicks {W F reserve : ℕ} (g : Context W F reserve) : ℕ:=
 movementCost g+UniformConditionalSectorLoop.budget actualCost (UniformProducedSectorChildABI.states g.physical)+
 213*g.inverse.layout.total+W*(16*g.inverse.layout.total+12)+
 (12*W+20)*(UniformProducedSectorChildABI.states g.physical).length+90
lemma kernelTicks_value {W F reserve : ℕ} (g : Context W F reserve) :
 kernelTicks g=overhead g+UniformConditionalSectorLoop.budget actualCost (UniformProducedSectorChildABI.states g.physical):=by
 unfold kernelTicks overhead;omega

/-- The actual metadata DFS, movement/gather/scatter/inverse and every header
term fit a fixed linear-volume allowance. No count of axes multiplies it. -/
lemma overhead_linear {W F reserve : ℕ} (g : Context W F reserve) :
 overhead g ≤ (400*W+1000)*g.packing.volume:=by
 have metadata:=UniformMultiAxisSectorMetadataPreparation.execution_cost g.physical g.metadata
  g.metadataLength (g.physicalVolume.trans g.packingVolume)
 rw [←g.packingVolume] at metadata
 have count: (UniformProducedSectorChildABI.states g.physical).length ≤ g.packing.volume:=
  (states_count (UniformSectorPackingMachine.physicalAxes g.physical)).trans_eq g.physicalVolume
 have positive:1 ≤ g.packing.volume:=
  (volume_one (UniformSectorPackingMachine.physicalAxes g.physical)).trans_eq g.physicalVolume
 have first:=Nat.mul_le_mul_left (12*W+44) count
 have second:=Nat.mul_le_mul_left (12*W+20) count
 have fixed:=Nat.mul_le_mul_left (43*W+163) positive
 unfold overhead movementCost
 rw [←g.inverseVolume,←g.packingVolume]
 nlinarith only [metadata,first,second,fixed]

noncomputable def clockConstant (W : ℕ) : ℝ:=densityConstant+400*W+1014
lemma clockConstant_nonneg (W : ℕ) : 0 ≤ clockConstant W:=by
 unfold clockConstant;have positive:=density_nonneg;positivity

/-- The real initialized same-child kernel cost, including its true sector
list and all movement/return controls, has one theta density per global tick. -/
theorem kernel_ticks_bound {W F reserve : ℕ} (g : Context W F reserve) :
 (kernelTicks g:ℝ) ≤ clockConstant W*(g.physical.length+1:ℝ)^UniformExponent.theta*g.packing.volume:=by
 have calls:=sector_budget (UniformSectorPackingMachine.physicalAxes g.physical)
 change (UniformConditionalSectorLoop.budget actualCost (UniformProducedSectorChildABI.states g.physical):ℝ) ≤
  (densityConstant*((UniformSectorPackingMachine.physicalAxes g.physical).length+1:ℝ)^UniformExponent.theta+14)*
   UniformSectorPackingMachine.physicalVolume g.physical at calls
 rw [g.physicalVolume,show (UniformSectorPackingMachine.physicalAxes g.physical).length=g.physical.length by simp [UniformSectorPackingMachine.physicalAxes]] at calls
 have localBound : (overhead g:ℝ) ≤ ((400*W+1000:ℕ):ℝ)*g.packing.volume:=by exact_mod_cast overhead_linear g
 have one:=UniformNetworkCost.exponentFactor_one_le g.physical.length
 have absorb:=mul_le_mul_of_nonneg_right
  (mul_le_mul_of_nonneg_left one (show (0:ℝ) ≤ 400*W+1014 by positivity))
  (Nat.cast_nonneg g.packing.volume)
 rw [kernelTicks_value,Nat.cast_add]
 unfold clockConstant
 push_cast at localBound
 nlinarith only [calls,localBound,absorb]

end
end ExactFourierCircuits.UniformActualKernelCost

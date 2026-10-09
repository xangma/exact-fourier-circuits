import DFTModelCRTGeometry
import UniformSelectedPhysicalCRT

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCRT
open OAI.PowerSaving
open UniformCRTTraversalCycle UniformCRTTraversalMachine UniformGenericPhysicalCoordinate
open UniformSelectedPhysicalCRT
open scoped BigOperators
noncomputable section

/-- Real selected CRT weights, enumerated in the physical MSB order. -/
def selectedCartesian (n : ℕ) : Tape (ℕ × ℕ) :=
  finiteCartesian (len n) (radices n) (alphaWeights n) (betaWeights n)

@[simp] theorem selectedCartesian_length (n : ℕ) :
    (selectedCartesian n).len = len n := by
  simp only [selectedCartesian,finiteCartesian_length,UniformSelectedCRT.radices_product]

/-- The Cartesian values are exactly the same AP/BP permutations used by the
actual physical Fourier theorem; no independently chosen codec is supplied. -/
theorem selectedCartesian_value (n : ℕ) (p : Fin (len n)) :
    (selectedCartesian n).look p.val (0,0) =
      ((physicalAlpha n p).val,(physicalBeta n p).val) := by
  let ds := (physicalOrdinal n).symm p
  have orderEq : ordinalEquiv n (rho n p) = ds := by
    exact congrArg (fun e => e p) (ordinal_rho n)
  have coordinate : (physical (radices n) ds).val = p.val := by
    have h := (physicalOrdinal n).apply_symm_apply p
    exact congrArg Fin.val h
  have lookup := finiteCartesian_coordinate (len n) (radices n)
    (UniformSelectedCRT.radix_pos n) (alphaWeights n) (betaWeights n) ds
  rw [coordinate] at lookup
  have alphaEq : (physicalAlpha n p).val =
      weightedAddress (len n) (alphaWeights n) (fun i => (ds i).val) := by
    change UniformCRT.address (radices n) (ordinalEquiv n (rho n p)) = _
    rw [orderEq]
    unfold UniformCRT.address weightedAddress
    rw [UniformSelectedCRT.radices_product]
  have betaEq : (physicalBeta n p).val =
      weightedAddress (len n) (betaWeights n) (fun i => (ds i).val) := by
    change UniformCRT.address (radices n)
      (outputDigits (radices n) (UniformSelectedCRT.radix_pos n) (ordinalEquiv n (rho n p))) = _
    rw [orderEq,←betaAddress_crt (radices n) (UniformSelectedCRT.radix_pos n)
      (UniformSelectedCRT.radices_pairwise n)]
    unfold betaAddress weightedAddress
    rw [UniformSelectedCRT.radices_product]
  exact lookup.trans (by rw [alphaEq,betaEq])

/-- Genuine row metadata identifies the executable recursion's selected tables. -/
theorem prefix_selectedCartesian (n : ℕ) (x : Args.T) (volumeEq : x.2.1 = len n)
    (rows : ∀ i : Fin (UniformAllAxisSeedPreparation.axisCount n),
      x.2.2.look (x.1+i.val) (0,(0,0)) =
        (radices n i,(alphaWeights n i,betaWeights n i))) :
    prefixTable (UniformAllAxisSeedPreparation.axisCount n) x = selectedCartesian n :=
  prefix_finiteCartesian (len n) (radices n) (alphaWeights n) (betaWeights n) x volumeEq rows

end
end ExactFourierCircuits.DFTModelCRT

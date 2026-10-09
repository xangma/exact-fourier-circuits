import UniformPhysicalCRTCoordinates
import UniformFinalNumericJoin
import UniformAllAxisSeedPreparation
import UniformProducedPhysicalCoordinate

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2 (5.5), PDF p.22 (`eq:crt-fourier`), with §4.2,
Lemma 4.1 and (4.3), PDF p.19 (`lem:sector-address`).

Connects CRT indices to the produced increasing-axis physical tensor codec.
The MSB ordering, directory cells and codec transport are implementation
bookkeeping around the paper's costed reindexing argument.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSelectedPhysicalCRT
open UniformCRTTraversalCycle UniformGenericPhysicalCoordinate UniformMachine
open OAI.ExactFourier
open scoped BigOperators
noncomputable section

/-- The retained increasing selected-axis list is encoded in actual physical
first-axis-most-significant tensor order. -/
/- Paper stage: Implementation codec bookkeeping around §4.2 (4.3), PDF p.19 and §5.2 (5.5), PDF p.22: actual increasing-axis physical order. -/
def physicalOrdinal (n:ℕ):((i:Fin (UniformAllAxisSeedPreparation.axisCount n))→Fin (radices n i))≃Fin (len n):=
 (physical (radices n)).trans (finCongr (UniformSelectedCRT.radices_product n))
/-- Coordinate of the genuine increasing-axis family, with only the proved
volume cast; no independent axis-order or codec assumption. -/
def producedOrdinal {n:ℕ} (f:UniformProducedAllAxisGeometry.Family n):
 ((i:Fin (UniformAllAxisSeedPreparation.axisCount n))→Fin (radices n i))≃Fin (len n):=
 (UniformPhysicalTensorFamily.coordinate
  (UniformSectorPackingMachine.physicalAxes (UniformProducedAllAxisGeometry.geometry f).physical)
  (UniformProducedAllAxisGeometry.index f) (UniformAllAxisSeedPreparation.radix n)
  (UniformProducedAllAxisGeometry.shape f)).trans
 (finCongr (((congrArg List.prod (UniformProducedPhysicalCoordinate.radices f)).trans
  (by simp only[List.prod_ofFn])).trans (UniformSelectedCRT.radices_product n)))
lemma producedOrdinal_eq {n:ℕ} (f:UniformProducedAllAxisGeometry.Family n):
 producedOrdinal f=physicalOrdinal n:=by
 ext ds
 simpa only[producedOrdinal,physicalOrdinal,Equiv.trans_apply,finCongr_apply,Fin.val_cast]
  using congrArg Fin.val (UniformProducedPhysicalCoordinate.actual_family f ds)
def rho (n:ℕ):Fin (len n)≃Fin (len n):=
 (physicalOrdinal n).symm.trans (ordinalEquiv n).symm
def physicalAlpha (n:ℕ):Fin (len n)≃Fin (len n):=(rho n).trans (alphaPermutation n)
def physicalBeta (n:ℕ):Fin (len n)≃Fin (len n):=(rho n).trans (betaPermutation n)
lemma rho_value (n:ℕ) (p:Fin (len n)):
 (rho n p).val=UniformPhysicalCRTArithmetic.normal (radices n) p.val:=by
 change (UniformPhysicalCRTCoordinates.rho (radices n) (UniformSelectedCRT.radix_pos n)
  ((finCongr (UniformSelectedCRT.radices_product n)).symm p)).val=_
 exact UniformPhysicalCRTCoordinates.rho_value _ _ _
lemma ordinal_rho (n:ℕ):(rho n).trans (ordinalEquiv n)=(physicalOrdinal n).symm:=by
 ext p
 simp only[rho,Equiv.trans_apply,Equiv.apply_symm_apply]
/- Paper stage: §5.2 (5.5), PDF p.22: AP input and BP output corrections turn the tensor of canonical local DFTs into the standard working DFT. -/
lemma physical_fourier (n:ℕ):
 UniformFinalNumericJoin.physicalFourier (physicalAlpha n) (physicalBeta n)=
 Matrix.reindex (physicalOrdinal n) (physicalOrdinal n)
  (PiTensor.matrix (fun i:Fin (UniformAllAxisSeedPreparation.axisCount n)=>fourierMatrix (radices n i))):=by
 have h:=UniformFinalNumericJoin.crt_physical_matrix n (rho n)
 rw[ordinal_rho] at h
 exact h
lemma physical_action (n:ℕ) (f:Fin (len n)→ℂ) (p:Fin (len n)):
 (UniformFinalNumericJoin.physicalFourier (physicalAlpha n) (physicalBeta n)).mulVec
  (fun q=>f (physicalAlpha n q)) p=(fourierMatrix (len n)).mulVec f (physicalBeta n p):=
 UniformFinalNumericJoin.physicalFourier_action _ _ _ _

/-- The decoder's radix reads are conclusions of genuine retained startup
seed directory cells, rather than a supplied coordinate conversion table. -/
/- Paper stage: Implementation initialization obligation for §5.2 index traversal, PDF p.22: radix reads come from actual retained startup cells. -/
lemma retained_directory (n:ℕ) (s:State)
 (retained:UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s):
 ∀i:Fin (UniformAllAxisSeedPreparation.axisCount n),s.natHeap (UniformAllAxisSeedPreparation.directoryBase n+2*i.val+1)=some (radices n i):=by
 intro i
 exact retained.width i i.isLt
end
end ExactFourierCircuits.UniformSelectedPhysicalCRT

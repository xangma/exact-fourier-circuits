import UniformFastPhysicalCRTVisits
import UniformSelectedPhysicalCRT
import UniformMultiAxisSectorMetadataPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFastPhysicalCRTArithmetic
open UniformCRTTraversalCycle
open scoped BigOperators
noncomputable section

lemma rho_value {a:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i)(p:Fin (∏i,r i)):
 normal r p.val=(UniformPhysicalCRTCoordinates.rho r hr p).val:=by
 rw[normal_eq]
 exact (UniformPhysicalCRTCoordinates.rho_value r hr p).symm
lemma selected_normal (n:ℕ)(p:Fin (len n)):
 normal (radices n) p.val=(UniformSelectedPhysicalCRT.rho n p).val:=by
 rw[normal_eq]
 exact (UniformSelectedPhysicalCRT.rho_value n p).symm
lemma selected_totalVisits {n:ℕ}(hn:0<n):
 totalVisits (reverse (radices n)) (len n)<2*len n:=by
 simpa only[UniformSelectedCRT.radices_product] using
  reverse_totalVisits (radices n) (UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn)
lemma selected_prefixVisits {n:ℕ}(hn:0<n)(k:ℕ)(hk:k≤len n):
 totalVisits (reverse (radices n)) k<2*len n:=by
 have h:=reverse_prefixVisits (radices n)
  (UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn) k
  (by simpa only[UniformSelectedCRT.radices_product] using hk)
 simpa only[UniformSelectedCRT.radices_product] using h
end
end ExactFourierCircuits.UniformFastPhysicalCRTArithmetic

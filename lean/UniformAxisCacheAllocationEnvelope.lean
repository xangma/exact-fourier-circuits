import UniformAxisCacheAllocationMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheAllocationMachine
open UniformJointAllocation
noncomputable section
/-- The actual selected cache allocation fits the existing global word envelope.
No generated address or peak is supplied as an assumption. -/
lemma selected_wordBudget (c:Constants)(n:ℕ)(hn:0<n)
 (j:Fin (UniformJointCacheAllocation.ell n)):
 wordBudget (UniformAllAxisSeedPreparation.radix n j)
  (UniformJointCacheAllocation.natStart c n+
   UniformJointCacheAllocation.offsetSum (fun i=>UniformJointCacheExtent.natSize (UniformAllAxisSeedPreparation.radixAt n i)) j.val)
  (UniformJointCacheAllocation.scalarStart c n+
   UniformJointCacheAllocation.offsetSum (fun i=>UniformJointCacheExtent.scalarSize (UniformAllAxisSeedPreparation.radixAt n i)) j.val)
  ≤ envelope c n:=by
 let r:=UniformAllAxisSeedPreparation.radix n j
 have rad:r ≤ 4*n:=
  (UniformGlobalLocalPreparation.radix_le_length n j).trans (UniformWorkingLength.workingLength_upper hn).le
 have pow:n+2 ≤ (n+2)^19:=by
  have h:=Nat.pow_le_pow_right (show 1 ≤ n+2 by omega) (show 1 ≤ 19 by decide)
  simpa only [pow_one] using h
 have coeff:200000 ≤ 100000*(fixed c+1):=by have:=fixed_large c;omega
 have row:D.budget (2*r) 0+100 ≤ slab c n:=calc
  D.budget (2*r) 0+100 ≤ 200000*(n+2):=by unfold D.budget;omega
  _ ≤ 100000*(fixed c+1)*(n+2):=Nat.mul_le_mul_right _ coeff
  _ ≤ slab c n:=Nat.mul_le_mul_left _ pow
 have fit:=UniformJointCacheAllocation.axis_fit c n j
 have ends:=UniformJointCacheAllocation.ends_bound c n hn
 change (UniformJointCacheAllocation.axis c n j).endNat ≤ _ ∧
  (UniformJointCacheAllocation.axis c n j).endScalar ≤ _ at fit
 unfold UniformJointCacheAllocation.axis at fit
 dsimp only [wordBudget]
 unfold envelope
 dsimp only [r] at row
 omega
end
end ExactFourierCircuits.UniformAxisCacheAllocationMachine

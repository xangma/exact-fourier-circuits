import UniformFourierAxisWorkspace
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarWorkspaceOrder
open UniformAllAxisSeedPreparation UniformJointAllocation
noncomputable section

lemma nat_before (c:Constants) (n:ℕ) (i j:Fin (axisCount n)) (before:i.val<j.val):
 (UniformFourierAxisWorkspace.axis c n i).endNat≤(UniformFourierAxisWorkspace.axis c n j).selected:=by
 have h:=UniformFourierAxisWorkspace.prefix_mono n (show i.val+1≤j.val by omega)
 rw[UniformFourierAxisWorkspace.prefix_step,radixAt_eq n i] at h
 change _≤UniformFourierAxisWorkspace.Arena.natBase c n+UniformFourierAxisWorkspace.natPrefix n j.val
 dsimp only[UniformFourierAxisWorkspace.axis]
 rw[(UniformFourierAxisWorkspace.axis_ends _ _ _).1]
 exact (Nat.add_assoc _ _ _).le.trans (Nat.add_le_add_left h _)

lemma scalar_before (c:Constants) (n:ℕ) (i j:Fin (axisCount n)) (before:i.val<j.val):
 (UniformFourierAxisWorkspace.axis c n i).endScalar≤(UniformFourierAxisWorkspace.axis c n j).pool:=by
 have h:=prefix_mono n (show i.val+1≤j.val by omega)
 rw[prefix_succ,radixAt_eq n i] at h
 have scaled:=Nat.mul_le_mul_left 9 h
 change _≤UniformFourierAxisWorkspace.Arena.scalarBase c n+9*prefixSum n j.val
 dsimp only[UniformFourierAxisWorkspace.axis]
 rw[(UniformFourierAxisWorkspace.axis_ends _ _ _).2]
 calc
  UniformFourierAxisWorkspace.Arena.scalarBase c n+9*prefixSum n i.val+9*radix n i=
   UniformFourierAxisWorkspace.Arena.scalarBase c n+9*(prefixSum n i.val+radix n i):=by ring
  _≤_:=Nat.add_le_add_left scaled _

lemma directory_before (c:Constants) (n:ℕ):
 slab c n+2*axisCount n≤UniformFourierAxisWorkspace.Arena.natBase c n:=by
 change slab c n+2*axisCount n≤UniformJointCacheAllocation.natEnd c n
 unfold UniformJointCacheAllocation.natEnd UniformJointCacheAllocation.natStart
 exact Nat.le_add_right _ _
end
end ExactFourierCircuits.UniformCalendarWorkspaceOrder

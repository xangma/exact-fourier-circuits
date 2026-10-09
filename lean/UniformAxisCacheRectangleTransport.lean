import UniformAxisCachePhysical
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheRectangleTransport
open UniformMachine UniformJointAllocation UniformJointCacheAllocation
open UniformAllAxisSeedPreparation UniformLocalRequestPlan UniformLocalRequestGeometry
open UniformLocalCacheSlotConductorMachine UniformAxisCachePhysical

/-- Completed rectangle cache entries depend only on their own allocated
axis intervals, so later actual axes can retain their full Cached facts. -/
theorem complete {c n j qs R T}(g:UniformLocalRequestGeometry.Geometry c n j qs R T)(i:ℕ)(hi:i<qs.length)
 {s u:State}(h:Complete c n j qs R T g i hi s)(frame:Heaps c n j s u):
 Complete c n j qs R T g i hi u:=by
 intro t ht
 have roomSlots:slotPrefix n qs i+(t+1)≤UniformJointCacheExtent.capacity (radix n j):=by
  have fit:=g.prefix_bound (i+1) (by omega)
  rw [prefix_step n qs i hi] at fit
  omega
 have natFit:=Nat.mul_le_mul_left (3*radix n j+11) roomSlots
 have scalarFit:=Nat.mul_le_mul_left (9*radix n j) roomSlots
 rw [Nat.mul_add,Nat.mul_add,Nat.mul_one] at natFit scalarFit
 have after:(axis c n j).leafForward≤(axis c n j).endNat:=by
  dsimp only [axis,axisBank]
  omega
 have before:=control_after_tasks c n j
 obtain ⟨slot,hs,l,bl,contents⟩:=h t ht
 refine ⟨slot,hs,l,bl,contents.transport (cache_shift (g.slots i hi).cache t) ?_ ?_⟩
 · intro a lo high
   apply frame.nat a
   · change (axis c n j).control+(3*radix n j+11)*slotPrefix n qs i+(3*radix n j+11)*t≤a at lo
     omega
   · change a<(axis c n j).control+(3*radix n j+11)*slotPrefix n qs i+
      (3*radix n j+11)*t+(3*radix n j+11) at high
     have endpoint:(axis c n j).leafForward=(axis c n j).control+
      (3*radix n j+11)*UniformJointCacheExtent.capacity (radix n j):=rfl
     omega
 · intro a lo high
   apply frame.scalar a
   · change (axis c n j).pool+9*radix n j*slotPrefix n qs i+9*radix n j*t≤a at lo
     omega
   · change a<(axis c n j).pool+9*radix n j*slotPrefix n qs i+9*radix n j*t+9*radix n j at high
     have endpoint:(axis c n j).endScalar=(axis c n j).pool+
      9*radix n j*UniformJointCacheExtent.capacity (radix n j):=rfl
     omega

end ExactFourierCircuits.UniformAxisCacheRectangleTransport

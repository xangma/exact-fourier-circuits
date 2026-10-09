import UniformCanonicalCacheSlotContext
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCanonicalCacheSlotGeometry
open UniformJointAllocation UniformAllAxisSeedPreparation UniformLocalRectangleDescriptors
open UniformLocalCacheSlotConductorMachine
noncomputable section
lemma slot_bounds (K j : ℕ) (slot : UniformLocalCacheChronology.Slot)
 (hs : SlotWitness K j slot) : slot.depth < 8*K+7 ∧ slot.color < 11 := by
 obtain ⟨p,t,_,bound,rfl⟩:=hs
 have levels : UniformLocalReplayAssembly.levels (8*K+6) p ≤ 8*K+7 := by
  unfold UniformLocalReplayAssembly.levels UniformLocalReplaySlotMachine.levelCount
  split <;>omega
 have depth : t/11 ≤ 8*K+6 := by omega
 have color : t%11 < 11 := Nat.mod_lt _ (by decide)
 simp only [UniformLocalReplaySlotMachine.decodedSlot]
 split_ifs <;>omega

section PhaseArithmetic
attribute [local irreducible] Nat.mul
lemma phase_slot_arithmetic (K z : ℕ) (h : 55*(4*(8*K+6+1)+2) ≤ z) :
 5*(352*K+330) ≤ z := by
 omega
end PhaseArithmetic
lemma phase_slots {n : ℕ} (hn : 0 < n) (axisIndex : Fin (axisCount n)) (q : Row)
 (g : UniformJointCacheWorkspace.Geometry n axisIndex q) :
 5*(352*(W.original n q).exponent+330) ≤ W.stride n := by
 have fit:=UniformJointCacheWorkspace.phase_fit hn axisIndex q g
 rw [UniformLocalReplayAssembly.prefix_total] at fit
 exact phase_slot_arithmetic _ _ fit

lemma persistent_bounds (constants : Constants) {n : ℕ} (hn : 0 < n) (axisIndex : Fin (axisCount n))
 (k : ℕ) (hk : k ≤ UniformJointCacheExtent.capacity (radix n axisIndex)) :
 let a:=UniformJointCacheAllocation.axis constants n axisIndex
 let b:=UniformJointCacheAllocation.slot a k
 b.factor+9*(radix n axisIndex) ≤ 3*slab constants n ∧
 b.abi+7 ≤ 3*slab constants n ∧ slab constants n ≤ b.permutation ∧
 slab constants n ≤ b.factor := by
 have nf:=(UniformJointCacheAllocation.axis_fit constants n axisIndex).1.trans
  (UniformJointCacheAllocation.ends_bound constants n hn).1
 have sf:=(UniformJointCacheAllocation.axis_fit constants n axisIndex).2.trans
  (UniformJointCacheAllocation.ends_bound constants n hn).2
 have nt:=Nat.mul_le_mul_left (3*radix n axisIndex+11) hk
 have sc:=Nat.mul_le_mul_left (9*radix n axisIndex) hk
 have rb:=UniformJointCacheWorkspace.radix_linear hn axisIndex
 have low:=UniformJointCacheWorkspace.below_cache constants n
 dsimp only [UniformJointCacheAllocation.axis,UniformJointCacheAllocation.axisBank,
  UniformJointCacheAllocation.slot,UniformJointCacheAllocation.natStart,
  UniformJointCacheAllocation.scalarStart] at nf sf ⊢
 change 2000*W.stride n ≤ slab constants n at low
 constructor
 · omega
 constructor
 · omega
 constructor <;>omega
end
end ExactFourierCircuits.UniformCanonicalCacheSlotGeometry

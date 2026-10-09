import UniformLocalRequestControl
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalRequestGeometry
open UniformMachine UniformAllAxisSeedPreparation UniformJointAllocation
open UniformLocalRequestPlan UniformLocalCacheSlotConductorMachine
noncomputable section

lemma aBound (constants:Constants)(n:ℕ)(j:Fin (axisCount n))(qs:List Request)(i:ℕ)(hi:i<qs.length):
 (qs[i]'hi).row.a ≤ UniformCrossHeightPreparationMachine.widthOf (controller constants n j qs i).height:=by
 rw [controller,requestAt_eq qs i hi]
 exact (UniformCanonicalCacheSlotComplete.widths constants n j (qs[i]'hi).row _ _).1
lemma eBound (constants:Constants)(n:ℕ)(j:Fin (axisCount n))(qs:List Request)(i:ℕ)(hi:i<qs.length):
 (qs[i]'hi).row.e ≤ UniformCrossHeightPreparationMachine.widthOf (controller constants n j qs i).height:=by
 rw [controller,requestAt_eq qs i hi]
 exact (UniformCanonicalCacheSlotComplete.widths constants n j (qs[i]'hi).row _ _).2

/-- Only ordinary finite shape, disjoint interval and word-envelope facts.
Every row, timing value, coefficient, phase bank and cached output is obtained
by the actual program; none occurs as a field of this geometry record. -/
structure Geometry (constants:Constants)(n:ℕ)(j:Fin (axisCount n))(qs:List Request)(R T:ℕ):Prop where
 workspace:∀i (hi:i<qs.length),UniformJointCacheWorkspace.Geometry n j (qs[i]'hi).row
 slots:∀i (hi:i<qs.length),UniformLocalCacheSlotConductorMachine.Geometry (envelope constants n)
  (controller constants n j qs i) (qs[i]'hi).row (aBound constants n j qs i hi)
  (eBound constants n j qs i hi) (UniformJointCacheWorkspace.inverse n)
 capacity:slotPrefix n qs qs.length ≤ UniformJointCacheExtent.capacity (radix n j)
 rowsHigh:slab constants n ≤ R
 timesHigh:slab constants n ≤ T
 rowsBefore:R+7*qs.length ≤ (UniformJointCacheAllocation.axis constants n j).control
 timesAfter:(UniformJointCacheAllocation.axis constants n j).leafForward ≤ T
 rowsBound:R+7*qs.length ≤ envelope constants n
 timesBound:T+qs.length ≤ envelope constants n

def bank (constants:Constants)(n:ℕ)(j:Fin (axisCount n))(qs:List Request)(i:ℕ)(hi:i<qs.length):
 Fin (UniformToeplitzCrossDAG.bankSize (controller constants n j qs i).height.K)→ℂ:=
 UniformLocalRectangleCacheBindings.coefficientBank j (qs[i]'hi).row
  (UniformJointCacheWorkspace.original n (qs[i]'hi).row) (controller constants n j qs i)

def Complete (constants:Constants)(n:ℕ)(j:Fin (axisCount n))(qs:List Request)(R T:ℕ)
 (g:Geometry constants n j qs R T)(i:ℕ)(hi:i<qs.length)(s:State):Prop:=
 ∀k,k<slotCount n (qs[i]'hi).row→Cached (B:=envelope constants n)
  (controller constants n j qs i) (qs[i]'hi).row (aBound constants n j qs i hi)
  (eBound constants n j qs i hi) (bank constants n j qs i hi) (g.slots i hi).positive k s

lemma Complete.heaps {constants n j qs R T g i hi s u}
 (h:@Complete constants n j qs R T g i hi s)
 (nat:u.natHeap=s.natHeap)(scalar:u.scalarHeap=s.scalarHeap):Complete constants n j qs R T g i hi u:=by
 intro k hk
 exact (h k hk).heaps (cache_shift (g.slots i hi).cache k) nat scalar

lemma past_prefix (n:ℕ)(qs:List Request){i k:ℕ}(hi:i<qs.length)(hk:k≤qs.length)(old:i<k):
 slotPrefix n qs i+slotCount n (qs[i]'hi).row ≤ slotPrefix n qs k:=by
 rw [←prefix_step n qs i hi]
 exact prefix_mono n qs (by omega) hk

lemma Complete.retained {constants n j qs R T}(g:Geometry constants n j qs R T)
 {i k:ℕ}(hi:i<qs.length)(hk:k<qs.length)(old:i<k){s u:State}
 (h:Complete constants n j qs R T g i hi s)
 (nat:∀a,slab constants n≤a→a<(controller constants n j qs k).cachePermutation→u.natHeap a=s.natHeap a)
 (scalar:∀a,slab constants n≤a→a<(controller constants n j qs k).pool→u.scalarHeap a=s.scalarHeap a):
 Complete constants n j qs R T g i hi u:=by
 have order:=past_prefix n qs hi (Nat.le_of_lt hk) old
 have positiveNat:=Nat.mul_le_mul_left (3*radix n j+11) order
 have positiveScalar:=Nat.mul_le_mul_left (9*radix n j) order
 have before:slab constants n ≤ (UniformJointCacheAllocation.axis constants n j).control ∧
  slab constants n ≤ (UniformJointCacheAllocation.axis constants n j).pool:=by
  dsimp only [UniformJointCacheAllocation.axis,UniformJointCacheAllocation.axisBank,
   UniformJointCacheAllocation.natStart,UniformJointCacheAllocation.scalarStart]
  constructor <;>omega
 have pn:=positiveNat
 have ps:=positiveScalar
 rw [Nat.mul_add] at pn ps

 intro t ht
 obtain ⟨slot,hs,l,bl,contents⟩:=h t ht
 refine ⟨slot,hs,l,bl,contents.transport (cache_shift (g.slots i hi).cache t) ?_ ?_⟩
 · intro a lo high
   apply nat a
   · change (UniformJointCacheAllocation.axis constants n j).control+
      (3*radix n j+11)*(slotPrefix n qs i)+(3*radix n j+11)*t≤a at lo
     omega
   · change a<(UniformJointCacheAllocation.axis constants n j).control+
      (3*radix n j+11)*slotPrefix n qs k
     change a<(UniformJointCacheAllocation.axis constants n j).control+
      (3*radix n j+11)*slotPrefix n qs i+(3*radix n j+11)*t+(3*radix n j+11) at high
     have tbound:=Nat.mul_le_mul_left (3*radix n j+11) (show t+1 ≤ slotCount n (qs[i]'hi).row by omega)
     rw [Nat.mul_add,Nat.mul_one] at tbound
     omega
 · intro a lo high
   apply scalar a
   · change (UniformJointCacheAllocation.axis constants n j).pool+
      9*radix n j*slotPrefix n qs i+9*radix n j*t≤a at lo
     omega
   · change a<(UniformJointCacheAllocation.axis constants n j).pool+
      9*radix n j*slotPrefix n qs k
     change a<(UniformJointCacheAllocation.axis constants n j).pool+
      9*radix n j*slotPrefix n qs i+9*radix n j*t+9*radix n j at high
     have tbound:=Nat.mul_le_mul_left (9*radix n j) (show t+1 ≤ slotCount n (qs[i]'hi).row by omega)
     rw [Nat.mul_add,Nat.mul_one] at tbound
     omega
end
end ExactFourierCircuits.UniformLocalRequestGeometry

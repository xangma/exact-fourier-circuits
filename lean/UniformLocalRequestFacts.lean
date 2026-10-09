import UniformLocalRequestGeometry
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalRequestGeometry
open UniformMachine UniformAllAxisSeedPreparation UniformJointAllocation
open UniformLocalRequestPlan UniformLocalCacheSlotConductorMachine
noncomputable section

lemma Geometry.prefix_bound {constants n j qs R T}(g:Geometry constants n j qs R T)
 (i:ℕ)(hi:i ≤ qs.length):slotPrefix n qs i ≤ UniformJointCacheExtent.capacity (radix n j):=
 (prefix_mono n qs hi le_rfl).trans g.capacity

lemma Geometry.end_before_leaf {constants n j qs R T}(g:Geometry constants n j qs R T)
 (i:ℕ)(hi:i<qs.length):
 (controller constants n j qs i).cachePermutation+
  (3*(controller constants n j qs i).ambient+11)*(352*(controller constants n j qs i).height.K+330)
  ≤  (UniformJointCacheAllocation.axis constants n j).leafForward:=by
 have cap:=g.prefix_bound (i+1) (by omega)
 rw[prefix_step n qs i hi] at cap
 have mult:=Nat.mul_le_mul_left (3*radix n j+11) cap
 rw[Nat.mul_add] at mult
 rw[controller,requestAt_eq qs i hi]
 change (UniformJointCacheAllocation.axis constants n j).control+
  (3*radix n j+11)*slotPrefix n qs i+(3*radix n j+11)*slotCount n (qs[i]'hi).row ≤ 
  (UniformJointCacheAllocation.axis constants n j).control+
   (3*radix n j+11)*UniformJointCacheExtent.capacity (radix n j)
 omega

lemma Geometry.scalar_end {constants n j qs R T}(g:Geometry constants n j qs R T)
 (i:ℕ)(hi:i<qs.length):
 (controller constants n j qs i).pool+
  9*(controller constants n j qs i).ambient*(352*(controller constants n j qs i).height.K+330)
 ≤ (UniformJointCacheAllocation.axis constants n j).endScalar:=by
 have cap:=g.prefix_bound (i+1) (by omega)
 rw[prefix_step n qs i hi] at cap
 have mult:=Nat.mul_le_mul_left (9*radix n j) cap
 rw[Nat.mul_add] at mult
 rw[controller,requestAt_eq qs i hi]
 change (UniformJointCacheAllocation.axis constants n j).pool+
  9*radix n j*slotPrefix n qs i+9*radix n j*slotCount n (qs[i]'hi).row≤
  (UniformJointCacheAllocation.axis constants n j).pool+
   9*radix n j*UniformJointCacheExtent.capacity (radix n j)
 omega

lemma Geometry.binding {constants n j qs R T}(_g:Geometry constants n j qs R T)
 (i:ℕ)(hi:i<qs.length):
 UniformLocalRectangleCacheBindings.Bindings (controller constants n j qs i) (qs[i]'hi).row
  (UniformJointCacheWorkspace.original n (qs[i]'hi).row) (UniformJointCacheWorkspace.lowRow n)
  (UniformJointCacheWorkspace.control n) (UniformJointCacheWorkspace.conjugate n)
  (UniformJointCacheWorkspace.falseRows n) (UniformJointCacheWorkspace.falseColors n)
  (UniformJointCacheWorkspace.falsePalette n) (UniformJointCacheWorkspace.falseDirectory n):=by
 rw[controller,requestAt_eq qs i hi]
 exact UniformLocalStoredRequestGeometry.binding constants n j _ _ _

lemma Geometry.prefixes {constants n j qs R T}(g:Geometry constants n j qs R T)(hn:0<n)
 (i:ℕ)(hi:i<qs.length):
 UniformLocalCacheContextConductor.Prefixes n (controller constants n j qs i):=by
 rw[controller,requestAt_eq qs i hi]
 exact UniformLocalStoredRequestGeometry.prefixes constants hn j _ _ _
  (g.prefix_bound i (Nat.le_of_lt hi))

def WorkspaceBound {B:ℕ}{c:Header.Parameters}{q:UniformLocalRectangleDescriptors.Row}
 {ha:q.a  ≤  UniformCrossHeightPreparationMachine.widthOf c.height}
 {he:q.e  ≤  UniformCrossHeightPreparationMachine.widthOf c.height}{I:ℕ}
 (g:UniformLocalCacheSlotConductorMachine.Geometry B c q ha he I)(H:ℕ):Prop:=
 ∀k (hk:k<352*c.height.K+330) slot (witness:SlotWitness c.height.K k slot),
 UniformLocalFactorDispatchMachine.natEnd (Cursor.shifted c k) q slot
  (g.layout k hk slot witness) (g.broadcast k hk) ha he I  ≤  H

lemma workspace_end (constants:Constants){n:ℕ}(hn:0<n)(j:Fin (axisCount n))
 (q:UniformLocalRectangleDescriptors.Row)(wg:UniformJointCacheWorkspace.Geometry n j q)
 (k0 time:ℕ)(c:Header.Parameters)
 (eq:c=UniformCanonicalCacheSlotGeometry.context constants n j q k0 time)
 (k:ℕ)(slot:UniformLocalCacheChronology.Slot)
 (l:UniformForwardMatchingFactorPreparation.Layout (Header.forward (Cursor.shifted c k) q slot) (envelope constants n))
 (b:UniformLocalFactorDispatchMachine.BroadcastLayout (Cursor.shifted c k) q (envelope constants n))
 (ha:q.a  ≤  UniformCrossHeightPreparationMachine.widthOf c.height)
 (he:q.e  ≤  UniformCrossHeightPreparationMachine.widthOf c.height):
 UniformLocalFactorDispatchMachine.natEnd (Cursor.shifted c k) q slot l b ha he
  (UniformJointCacheWorkspace.inverse n)  ≤  slab constants n:=by
 subst c
 exact (UniformCanonicalCacheSlotComplete.output_ends constants hn j q wg k0 time k slot l b ha he).2

lemma Geometry.workspaces {constants n j qs R T}(g:Geometry constants n j qs R T)(hn:0<n)
 (i:ℕ)(hi:i<qs.length):WorkspaceBound (g.slots i hi) (slab constants n):=by
 intro k hk slot witness
 have eq:controller constants n j qs i=UniformCanonicalCacheSlotGeometry.context constants n j
  (qs[i]'hi).row (slotPrefix n qs i) (qs[i]'hi).time:=by rw[controller,requestAt_eq qs i hi]
 exact workspace_end constants hn j (qs[i]'hi).row (g.workspace i hi) (slotPrefix n qs i)
  (qs[i]'hi).time (controller constants n j qs i) eq k slot
  ((g.slots i hi).layout k hk slot witness) ((g.slots i hi).broadcast k hk)
  (aBound constants n j qs i hi) (eBound constants n j qs i hi)

lemma Geometry.total {constants n j qs R T}(g:Geometry constants n j qs R T)
 (i:ℕ)(hi:i<qs.length):352*(controller constants n j qs i).height.K+330 ≤ envelope constants n:=by
 have controls:=(g.slots i hi).inputs.controls
 have before:=(g.slots i hi).inputs.cache
 have bound: (controller constants n j qs i).cachePermutation ≤ envelope constants n:=by
  simpa only[Cursor.shifted,UniformLocalCacheSlotCursorMachine.cursorParameters,Nat.mul_zero,Nat.add_zero]
   using ((g.slots i hi).endpoints 0 (by omega)).2.2.2.1
 have count:=UniformLocalReplayStoredSlots.slot_count (controller constants n j qs i).height.K
 omega

lemma Geometry.source_retained {constants n j qs R T}(g:Geometry constants n j qs R T)
 (i:ℕ)(hi:i<qs.length){s u:State}(src:Source R T qs s)
 (low:∀a,slab constants n ≤ a → a<(controller constants n j qs i).cachePermutation → u.natHeap a=s.natHeap a)
 (high:∀a,slab constants n ≤ a → 
  (controller constants n j qs i).cachePermutation+(3*(controller constants n j qs i).ambient+11)*
   (352*(controller constants n j qs i).height.K+330) ≤ a → u.natHeap a=s.natHeap a):
 Source R T qs u:=by
 apply src.transport
 · intro k hk f
   apply low
   · have:=g.rowsHigh;omega
   · have before:=g.rowsBefore
     change R+7*k+f.val<(UniformJointCacheAllocation.axis constants n j).control+
      (3*radix n j+11)*slotPrefix n qs i
     have:=f.isLt
     omega
 · intro k hk
   apply high
   · have:=g.timesHigh;omega
   · exact (g.end_before_leaf i hi).trans (by have:=g.timesAfter;omega)

lemma small_budgets (constants:Constants){n:ℕ}(hn:0<n)(j:Fin (axisCount n)):
 9*radix n j ≤ envelope constants n ∧3*radix n j+11 ≤ envelope constants n:=by
 have size:=UniformJointCacheWorkspace.radix_linear hn j
 have envelope:=UniformJointCacheWorkspace.ambient_budget constants n
 change 2000*UniformJointCacheWorkspace.stride n ≤ UniformJointAllocation.envelope constants n at envelope
 omega

lemma low_before_cache (constants:Constants)(n:ℕ):
 UniformJointCacheWorkspace.lowRow n+7 ≤ slab constants n ∧
 22*UniformJointCacheWorkspace.stride n+1<slab constants n:=by
 have low:=UniformJointCacheWorkspace.below_cache constants n
 have positive:0<UniformJointCacheWorkspace.stride n:=pow_pos (show 0<n+2 by omega) 19
 change 2000*UniformJointCacheWorkspace.stride n ≤ slab constants n at low
 change UniformJointCacheWorkspace.stride n+7 ≤ slab constants n ∧
  22*UniformJointCacheWorkspace.stride n+1<slab constants n
 omega

lemma scalar_prior {constants n j qs R T}(_g:Geometry constants n j qs R T)
 (i:ℕ)(_hi:i<qs.length){s u:State}
 (scalar:∀a,slab constants n ≤ a → 
  (a<(controller constants n j qs i).pool ∨ (controller constants n j qs i).pool+
   9*(controller constants n j qs i).ambient*(352*(controller constants n j qs i).height.K+330) ≤ a) → 
  a ≠ (controller constants n j qs i).mu → a ≠ (controller constants n j qs i).conjugateMu → u.scalarHeap a=s.scalarHeap a):
 ∀a,slab constants n ≤ a → a<(controller constants n j qs i).pool → u.scalarHeap a=s.scalarHeap a:=by
 intro a low before
 have temp:=(low_before_cache constants n).2
 apply scalar a low (Or.inl before)
 · change a ≠ 22*UniformJointCacheWorkspace.stride n
   omega
 · change a ≠ 22*UniformJointCacheWorkspace.stride n+1
   omega

end
end ExactFourierCircuits.UniformLocalRequestGeometry

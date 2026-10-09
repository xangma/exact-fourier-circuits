import UniformCanonicalCacheSlotLayout
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCanonicalCacheSlotComplete
open UniformJointAllocation UniformAllAxisSeedPreparation UniformLocalRectangleDescriptors
open UniformCanonicalCacheSlotGeometry UniformCanonicalCacheSlotPreparation
open UniformLocalCacheSlotConductorMachine UniformLocalFactorDispatchMachine
noncomputable section
attribute [local irreducible] Nat.mul

lemma widths (constants : Constants) (n : ℕ) (axisIndex : Fin (axisCount n)) (q : Row) (k time : ℕ) :
 q.a ≤ UniformCrossHeightPreparationMachine.widthOf (context constants n axisIndex q k time).height ∧
 q.e ≤ UniformCrossHeightPreparationMachine.widthOf (context constants n axisIndex q k time).height :=
 UniformSeedHeightPreparation.widths (UniformJointCacheWorkspace.original n q)

lemma output_ends (constants : Constants) {n : ℕ} (hn : 0<n) (axisIndex : Fin (axisCount n))
 (q : Row) (g : UniformJointCacheWorkspace.Geometry n axisIndex q) (k time j : ℕ)
 (slot : UniformLocalCacheChronology.Slot)
 (l : UniformForwardMatchingFactorPreparation.Layout
  (Header.forward (Cursor.shifted (context constants n axisIndex q k time) j) q slot) (envelope constants n))
 (bl : BroadcastLayout (Cursor.shifted (context constants n axisIndex q k time) j) q (envelope constants n))
 (ha : q.a ≤ UniformCrossHeightPreparationMachine.widthOf (context constants n axisIndex q k time).height)
 (he : q.e ≤ UniformCrossHeightPreparationMachine.widthOf (context constants n axisIndex q k time).height) :
 printedBase (Cursor.shifted (context constants n axisIndex q k time) j) slot (UniformJointCacheWorkspace.inverse n)+
  3*(printedRows (Cursor.shifted (context constants n axisIndex q k time) j) q slot l bl ha he).length ≤ slab constants n ∧
 natEnd (Cursor.shifted (context constants n axisIndex q k time) j) q slot l bl ha he (UniformJointCacheWorkspace.inverse n) ≤ slab constants n := by
 let c:=Cursor.shifted (context constants n axisIndex q k time) j
 let z:=UniformJointCacheWorkspace.stride n
 have geometry:=dispatched_geometry c q slot l bl ha he
 have cap:=UniformMatchingAxisTableMachine.matching_capacity c.ambient
  (UniformGlobalMatchingScaleBankBridge.rowEdges (printedRows c q slot l bl ha he) geometry.2.1)
  (UniformGlobalMatchingScaleBankBridge.rowEdges_matching _ _ geometry.2.2)
  (UniformGlobalMatchingScaleBankBridge.rowEdges_range c.ambient _ _ geometry.1)
 have radixBound : 100*radix n axisIndex+1000 ≤ z := UniformJointCacheWorkspace.radix_linear hn axisIndex
 have low:=UniformJointCacheWorkspace.below_cache constants n
 change 2000*z ≤ slab constants n at low
 change 2*(printedRows c q slot l bl ha he).length ≤ radix n axisIndex at cap
 have ar : q.a≤radix n axisIndex := by have:=g.hRows;omega
 have translated : c.translated=31*z := rfl
 constructor
 · change printedBase c slot (32*z)+3*(printedRows c q slot l bl ha he).length ≤ slab constants n
   by_cases b:slot.broadcast=true <;> by_cases i:slot.inverse=true
   all_goals simp only [printedBase,b,i,translated,Bool.false_eq_true,ite_false,ite_true]
   all_goals omega
 · change natEnd c q slot l bl ha he (32*z) ≤ slab constants n
   by_cases b:slot.broadcast=true <;> by_cases i:slot.inverse=true
   all_goals simp only [natEnd,b,i,translated,Bool.false_eq_true,ite_false,ite_true]
   all_goals simp only [printedRows,b,i,Bool.false_eq_true,ite_false,ite_true] at cap
   all_goals omega

/-- Canonical ordinary geometry of the actual2308 banks and actual1336 slot loop.
The only remaining prefix assumptions are integer cache/time intervals. -/
theorem geometry (constants : Constants) {n : ℕ} (hn : 0<n) (axisIndex : Fin (axisCount n))
 (v o : ℕ) (q : Row) (hv : 2≤v) (hp : 0<UniformWorkspacePlanner.selected v)
 (extent : o+v ≤ radix n axisIndex) (member : q∈rows v o (UniformWorkspacePlanner.selected v))
 (k time : ℕ)
 (cacheRoom : k+(352*(UniformJointCacheWorkspace.original n q).exponent+330) ≤ UniformJointCacheExtent.capacity (radix n axisIndex))
 (timeRoom : time+28*(352*(UniformJointCacheWorkspace.original n q).exponent+330) ≤ envelope constants n)
 (ha : q.a ≤ UniformCrossHeightPreparationMachine.widthOf (context constants n axisIndex q k time).height)
 (he : q.e ≤ UniformCrossHeightPreparationMachine.widthOf (context constants n axisIndex q k time).height) :
 Geometry (envelope constants n) (context constants n axisIndex q k time) q ha he (UniformJointCacheWorkspace.inverse n) := by
 let c:=context constants n axisIndex q k time
 let z:=UniformJointCacheWorkspace.stride n
 have g:=UniformJointCacheWorkspace.geometry_of_rows axisIndex q hv hp (show v≤radix n axisIndex by omega) member
 have room : k≤UniformJointCacheExtent.capacity (radix n axisIndex) := by omega
 have size:=UniformCanonicalCacheSlotLayout.linear hn axisIndex q g
 change 100*((UniformJointCacheWorkspace.original n q).exponent+
  (UniformJointCacheWorkspace.original n q).width+(UniformJointCacheWorkspace.original n q).gates+q.a+q.e+1)+1000 ≤ z at size
 have low:=UniformJointCacheWorkspace.below_cache constants n
 change 2000*z ≤ slab constants n at low
 have budget:=UniformJointCacheWorkspace.ambient_budget constants n
 change 2000*z ≤ envelope constants n at budget
 have high:=persistent_bounds constants hn axisIndex k room
 change _∧_∧slab constants n≤c.cachePermutation∧slab constants n≤c.pool at high
 let fl:=fun j (hj:j<352*c.height.K+330) slot (hs:SlotWitness c.height.K j slot) =>
  forward_layout constants hn axisIndex v o q hv hp extent member k time j slot cacheRoom timeRoom hj hs
 let bl:=fun j (hj:j<352*c.height.K+330) =>
  UniformCanonicalCacheSlotLayout.broadcast constants hn axisIndex v o q hv hp extent member k time j cacheRoom timeRoom hj
 have positive : 2≤radix n axisIndex := by omega
 refine ⟨UniformCanonicalCacheSlotLayout.inputs constants hn axisIndex q g k time room,
  UniformCanonicalCacheSlotLayout.cache constants n axisIndex q k time,
  positive,fl,bl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · intro j hj slot hs
   exact UniformCanonicalCacheSlotLayout.inverse constants hn axisIndex q g k time j slot (fl j hj slot hs)
 · intro j hj slot hs
   have out:=(output_ends constants hn axisIndex q g k time j slot (fl j hj slot hs) (bl j hj) ha he).1
   have shiftedHigh:slab constants n ≤ (Cursor.shifted c j).cachePermutation := by
    change slab constants n ≤ (Cursor.shifted (context constants n axisIndex q k time) j).cachePermutation
    rw [(shifted_cache constants n axisIndex q k time j).2.1]
    exact (persistent_bounds constants hn axisIndex (k+j) (by
     have sj : j≤352*(UniformJointCacheWorkspace.original n q).exponent+330 := Nat.le_of_lt hj
     omega)).2.2.1
   exact out.trans shiftedHigh
 · intro j hj slot hs
   exact (output_ends constants hn axisIndex q g k time j slot (fl j hj slot hs) (bl j hj) ha he).2.trans high.2.2.1
 · exact le_of_eq (UniformJointCacheAllocation.slot_regions (UniformJointCacheAllocation.axis constants n axisIndex) k).1
 · exact le_of_eq (UniformJointCacheAllocation.slot_regions (UniformJointCacheAllocation.axis constants n axisIndex) k).2.1
 · exact le_of_eq (UniformJointCacheAllocation.slot_regions (UniformJointCacheAllocation.axis constants n axisIndex) k).2.2.1
 · exact le_of_eq (UniformJointCacheAllocation.slot_regions (UniformJointCacheAllocation.axis constants n axisIndex) k).2.2.2
 · change z+6≤envelope constants n;omega
 · intro j hj
   exact (endpoint_bounds constants hn axisIndex q g k time j cacheRoom timeRoom (Nat.le_of_lt hj)).2.2.2.2.1
 · intro j hj
   exact (endpoint_bounds constants hn axisIndex q g k time j cacheRoom timeRoom (Nat.le_of_lt hj)).2.1
 · change 22*z<c.pool;omega
 · change 22*z+1<c.pool;omega
 · intro j hj
   have ends:=endpoint_bounds constants hn axisIndex q g k time j cacheRoom timeRoom hj
   exact ⟨by have:=ends.2.2.2.2.1;omega,by have:=ends.1;omega,
    ends.2.2.2.2.2.1,ends.2.2.2.2.2.2.1,ends.2.2.2.2.2.2.2.1,
    ends.2.2.2.2.2.2.2.2.1,ends.2.2.2.2.2.2.2.2.2,by have:=ends.2.1;omega⟩
end
end ExactFourierCircuits.UniformCanonicalCacheSlotComplete

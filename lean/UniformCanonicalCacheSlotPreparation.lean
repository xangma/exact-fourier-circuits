import UniformCanonicalCacheSlotGeometry
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCanonicalCacheSlotPreparation
open UniformJointAllocation UniformAllAxisSeedPreparation UniformLocalRectangleDescriptors
open UniformCanonicalCacheSlotGeometry UniformLocalCacheSlotConductorMachine
namespace W
abbrev original:=UniformJointCacheWorkspace.original
abbrev stride:=UniformJointCacheWorkspace.stride
end W
noncomputable section
attribute [local irreducible] Nat.mul

private lemma coarse_floor (x z : ℕ) (h : 100*x+1000 ≤ z) : 1000 ≤ z := by omega
private lemma coarse_linear (K N t V a e G z : ℕ)
 (h : 100*(K+N+t+V+a+e+G+1)+1000 ≤ z) :
 100*(K+N+G+a+e+1)+1000 ≤ z := by omega
private lemma code_bound (z B : ℕ) (h : 1000 ≤ z) (b : 2000*z ≤ B) : 415 ≤ B := by omega

lemma gates_eq (n : ℕ) (q : Row) :
 (W.original n q).gates=UniformWorkspacePlanner.gateCount q.a q.e := by
 dsimp only [W.original,UniformJointCacheWorkspace.original,UniformSeedHeightPreparation.Config.gates,
  UniformSeedHeightPreparation.Config.exponent,UniformSeedHeightPreparation.Config.width]
 rw [UniformWorkspacePlanner.gateCount_eq,UniformRadixTwoDAG.width_eq]

lemma shifted_cache (constants : Constants) (n : ℕ) (axisIndex : Fin (axisCount n))
 (q : Row) (k time j : ℕ) :
 let c:=Cursor.shifted (context constants n axisIndex q k time) j
 let b:=UniformJointCacheAllocation.slot (UniformJointCacheAllocation.axis constants n axisIndex) (k+j)
 c.pool=b.factor ∧ c.cachePermutation=b.permutation ∧ c.cacheWidths=b.widths ∧
 c.cacheMarkers=b.markers ∧ c.cacheAxis=b.physicalAxis ∧ c.cacheDirectory=b.abi := by
 dsimp only [Cursor.shifted,UniformLocalCacheSlotCursorMachine.cursorParameters,context,
  UniformJointCacheAllocation.slot,UniformJointCacheAllocation.axis,UniformJointCacheAllocation.axisBank]
 refine ⟨?_,?_,?_,?_,?_,?_⟩ <;>ring

lemma endpoint_bounds (constants : Constants) {n : ℕ} (hn : 0 < n) (axisIndex : Fin (axisCount n))
 (q : Row) (g : UniformJointCacheWorkspace.Geometry n axisIndex q) (k time j : ℕ)
 (cacheRoom : k+(352*(W.original n q).exponent+330) ≤ UniformJointCacheExtent.capacity (radix n axisIndex))
 (timeRoom : time+28*(352*(W.original n q).exponent+330) ≤ envelope constants n)
 (hj : j ≤ 352*(W.original n q).exponent+330) :
 let c:=Cursor.shifted (context constants n axisIndex q k time) j
 c.pool+9*c.ambient ≤ envelope constants n ∧ c.cacheDirectory+7 ≤ envelope constants n ∧
 slab constants n ≤ c.cachePermutation ∧ slab constants n ≤ c.pool ∧
 c.slot+4 ≤ envelope constants n ∧ c.time ≤ envelope constants n ∧
 c.cachePermutation ≤ envelope constants n ∧ c.cacheWidths ≤ envelope constants n ∧
 c.cacheMarkers ≤ envelope constants n ∧ c.cacheAxis ≤ envelope constants n := by
 have bounds:=persistent_bounds constants hn axisIndex (k+j) (by omega)
 have fields:=shifted_cache constants n axisIndex q k time j
 have regions:=UniformJointCacheAllocation.slot_regions (UniformJointCacheAllocation.axis constants n axisIndex) (k+j)
 have phase:=phase_slots hn axisIndex q g
 have budget:=UniformJointCacheWorkspace.ambient_budget constants n
 have linear:1000 ≤ W.stride n := coarse_floor _ _ (UniformJointCacheWorkspace.arithmetic hn axisIndex q g).1
 have wide : 3*slab constants n ≤ envelope constants n := by unfold envelope;omega
 change _∧_∧_∧_∧_∧_∧_∧_∧_∧_
 rw [fields.1,fields.2.1,fields.2.2.1,fields.2.2.2.1,fields.2.2.2.2.1,fields.2.2.2.2.2]
 change _∧_∧_∧_∧17*W.stride n+5*j+4 ≤ envelope constants n ∧
  time+28*j ≤ envelope constants n ∧_∧_∧_∧_
 have rr : (UniformJointCacheAllocation.axis constants n axisIndex).radix=radix n axisIndex := rfl
 rw [rr] at regions
 exact ⟨bounds.1.trans wide,bounds.2.1.trans wide,bounds.2.2.1,bounds.2.2.2,
  by change 2000*W.stride n ≤ envelope constants n at budget;omega,
  by omega,by omega,by omega,by omega,by omega⟩

/-- The row's own measured local width is used by all three actual branches. -/
lemma forward_layout (constants : Constants) {n : ℕ} (hn : 0 < n) (axisIndex : Fin (axisCount n))
 (v o : ℕ) (q : Row) (hv : 2 ≤ v) (hp : 0 < UniformWorkspacePlanner.selected v)
 (extent : o+v ≤ radix n axisIndex) (member : q ∈ rows v o (UniformWorkspacePlanner.selected v))
 (k time j : ℕ) (slot : UniformLocalCacheChronology.Slot)
 (cacheRoom : k+(352*(W.original n q).exponent+330) ≤ UniformJointCacheExtent.capacity (radix n axisIndex))
 (timeRoom : time+28*(352*(W.original n q).exponent+330) ≤ envelope constants n)
 (hj : j < 352*(W.original n q).exponent+330) (hs : SlotWitness (W.original n q).exponent j slot) :
 UniformForwardMatchingFactorPreparation.Layout
  (Header.forward (Cursor.shifted (context constants n axisIndex q k time) j) q slot) (envelope constants n) := by
 let c:=W.original n q
 let K:=c.exponent
 let N:=c.width
 let G:=c.gates
 let z:=W.stride n
 obtain ⟨a,e,target,split,interior,source,capacity,width,offset⟩:=
  UniformLocalRectangleBankMachine.rows_geometry v o q hv hp member
 have g:=UniformJointCacheWorkspace.geometry_of_rows axisIndex q hv hp (by omega) member
 have arithmetic:=UniformJointCacheWorkspace.arithmetic hn axisIndex q g
 have big := arithmetic.1
 change 100*(K+N+UniformRadixTwoDAG.count K+UniformConvolutionDAG.total K+q.a+q.e+G+1)+1000 ≤ z at big
 have linear : 100*(K+N+G+q.a+q.e+1)+1000 ≤ z := coarse_linear _ _ _ _ _ _ _ _ big
 have radixBound : 100*radix n axisIndex+1000 ≤ z := UniformJointCacheWorkspace.radix_linear hn axisIndex
 have G_eq : G=UniformWorkspacePlanner.gateCount q.a q.e := gates_eq n q
 have rowBound : 6*G*(8*K+7) ≤ z := arithmetic.2.2.2.2
 have budget:=UniformJointCacheWorkspace.ambient_budget constants n
 change 2000*z ≤ envelope constants n at budget
 have endpoints:=endpoint_bounds constants hn axisIndex q g k time j cacheRoom timeRoom (by omega)
 have slotRange:=slot_bounds K j slot hs
 have poolHigh:=endpoints.2.2.2.1
 have low:=UniformJointCacheWorkspace.below_cache constants n
 change 2000*z ≤ slab constants n at low
 constructor
 · constructor
   · omega
   · change 2 ≤ q.width;omega
   · change q.j0+q.e ≤ q.width;omega
   · change q.i0+q.a ≤ q.width;omega
   · change q.j0+q.e ≤ q.i0 ∨ q.i0+q.a ≤ q.j0;left;omega
   · change G+q.e+q.a ≤ q.width
     rw [G_eq]
     omega
   · change (if slot.enabled then 8*z else 18*z)+6*G*(8*K+7) ≤ 23*z
     split_ifs <;>omega
   · change (if slot.enabled then 9*z else 19*z)+2*G*(8*K+7) ≤ 23*z
     split_ifs <;>nlinarith only [rowBound]
   · change (if slot.enabled then 11*z else 21*z)+3*(8*K+7) ≤ 23*z
     split_ifs <;>omega
   · change 23*z+G ≤ 24*z;omega
   · change 24*z+6*G ≤ 25*z;omega
   · change 25*z+2*G ≤ 26*z;omega
   · change 26*z+6*G ≤ 27*z;omega
   · change 27*z+q.width ≤ 28*z
     omega
   · change 28*z+q.width ≤ 29*z
     omega
   · change 29*z+q.width ≤ 30*z
     omega
   · change 30*z+4 ≤ envelope constants n;omega
   · change slot.depth < 8*K+7;exact slotRange.1
   · change slot.color < 11;exact slotRange.2
 · change 30*z+4 ≤ 31*z;omega
 · change 31*z+6*G ≤ envelope constants n;omega
 · change q.offset+q.width ≤ radix n axisIndex;omega
 · constructor
   · change 4*z+(N+6*N) ≤ 5*z;omega
   · change 5*z+(N+6*N) ≤ 6*z;omega
   · change 6*z+6 ≤ 11*z;omega
   · change 11*z+(N+6*N) ≤ 22*z;omega
   · change 22*z < 22*z+1;omega
   · change 22*z+1 ≤ envelope constants n;omega
   · omega
 · change 6 ≤ 22*z;omega
 · change 22*z+1 < (Cursor.shifted (context constants n axisIndex q k time) j).pool
   omega
 · exact endpoints.1
 · exact code_bound z _ (coarse_floor _ _ linear) budget
end
end ExactFourierCircuits.UniformCanonicalCacheSlotPreparation

import UniformCanonicalCacheSlotPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCanonicalCacheSlotLayout
open UniformJointAllocation UniformAllAxisSeedPreparation UniformLocalRectangleDescriptors
open UniformCanonicalCacheSlotGeometry UniformCanonicalCacheSlotPreparation UniformLocalCacheSlotConductorMachine
noncomputable section
attribute [local irreducible] Nat.mul

private lemma weaken (K N t V a e G z : ℕ)
 (h : 100*(K+N+t+V+a+e+G+1)+1000 ≤ z) :
 100*(K+N+G+a+e+1)+1000 ≤ z := by omega

lemma linear {n : ℕ} (hn : 0<n) (axisIndex : Fin (axisCount n)) (q : Row)
 (g : UniformJointCacheWorkspace.Geometry n axisIndex q) :
 let c:=UniformJointCacheWorkspace.original n q
 100*(c.exponent+c.width+c.gates+q.a+q.e+1)+1000 ≤ UniformJointCacheWorkspace.stride n :=
 weaken _ _ _ _ _ _ _ _ (UniformJointCacheWorkspace.arithmetic hn axisIndex q g).1

lemma inputs (constants : Constants) {n : ℕ} (hn : 0<n) (axisIndex : Fin (axisCount n))
 (q : Row) (g : UniformJointCacheWorkspace.Geometry n axisIndex q) (k time : ℕ)
 (cacheRoom : k ≤ UniformJointCacheExtent.capacity (radix n axisIndex)) :
 InputLayout (context constants n axisIndex q k time) q := by
 let c:=UniformJointCacheWorkspace.original n q
 let z:=UniformJointCacheWorkspace.stride n
 have size:=linear hn axisIndex q g
 change 100*(c.exponent+c.width+c.gates+q.a+q.e+1)+1000 ≤ z at size
 have slots:=UniformJointCacheWorkspace.slots_before hn axisIndex q g
 have low:=UniformJointCacheWorkspace.below_cache constants n
 change 2000*z ≤ slab constants n at low
 have high:=(persistent_bounds constants hn axisIndex k cacheRoom).2.2.1
 constructor
 · change z+7 ≤ 23*z;omega
 · change 17*z+55*UniformLocalReplayAssembly.phasePrefix (8*c.exponent+6) 6 ≤ 23*z
   have control:=slots.2.2.1
   change 17*z+55*UniformLocalReplayAssembly.phasePrefix (8*c.exponent+6) 6 ≤ 18*z at control
   omega
 · exact (UniformJointCacheWorkspace.original_layout hn axisIndex q g).heightLayout
 · exact UniformJointCacheWorkspace.false_layout hn axisIndex q g
 · change 11*z+3*(8*c.exponent+7) ≤ 23*z;omega
 · change 21*z+3*(8*c.exponent+7) ≤ 23*z;omega
 · change 23*z ≤ (UniformJointCacheAllocation.slot (UniformJointCacheAllocation.axis constants n axisIndex) k).permutation
   omega

lemma cache (constants : Constants) (n : ℕ) (axisIndex : Fin (axisCount n)) (q : Row) (k time : ℕ) :
 CacheLayout (context constants n axisIndex q k time) := by
 have rr : (UniformJointCacheAllocation.axis constants n axisIndex).radix=radix n axisIndex := rfl
 constructor <;> dsimp only [context,UniformJointCacheAllocation.slot]
 all_goals rw [rr]
 all_goals omega

lemma broadcast (constants : Constants) {n : ℕ} (hn : 0<n) (axisIndex : Fin (axisCount n))
 (v o : ℕ) (q : Row) (hv : 2≤v) (hp : 0<UniformWorkspacePlanner.selected v)
 (extent : o+v ≤ radix n axisIndex) (member : q∈rows v o (UniformWorkspacePlanner.selected v))
 (k time j : ℕ)
 (cacheRoom : k+(352*(UniformJointCacheWorkspace.original n q).exponent+330) ≤ UniformJointCacheExtent.capacity (radix n axisIndex))
 (timeRoom : time+28*(352*(UniformJointCacheWorkspace.original n q).exponent+330) ≤ envelope constants n)
 (hj : j<352*(UniformJointCacheWorkspace.original n q).exponent+330) :
 UniformLocalFactorDispatchMachine.BroadcastLayout (Cursor.shifted (context constants n axisIndex q k time) j) q (envelope constants n) := by
 let c:=UniformJointCacheWorkspace.original n q
 let z:=UniformJointCacheWorkspace.stride n
 obtain ⟨a,e,target,split,interior,source,capacity,width,offset⟩:=
  UniformLocalRectangleBankMachine.rows_geometry v o q hv hp member
 have g:=UniformJointCacheWorkspace.geometry_of_rows axisIndex q hv hp (by omega) member
 have size:=linear hn axisIndex q g
 change 100*(c.exponent+c.width+c.gates+q.a+q.e+1)+1000 ≤ z at size
 have ends:=endpoint_bounds constants hn axisIndex q g k time j cacheRoom timeRoom (Nat.le_of_lt hj)
 have budget:=UniformJointCacheWorkspace.ambient_budget constants n
 change 2000*z ≤ envelope constants n at budget
 have gateCount:=gates_eq n q
 have outputCount : q.a≤c.gates := by
   change q.a ≤ 6*(3*c.exponent*c.width+2*c.width)+2*q.a
   omega
 constructor
 · change c.gates+q.e+q.a ≤ q.width
   rw [gateCount];omega
 · exact outputCount
 · omega
 · omega
 · change 23*z+c.gates ≤ 26*z;omega
 · change 26*z+3*q.a ≤ 31*z;omega
 · change 31*z+3*q.a ≤ envelope constants n;omega
 · change z+6 ≤ envelope constants n;omega
 · exact ends.2.2.2.2.1

lemma inverse (constants : Constants) {n : ℕ} (hn : 0<n) (axisIndex : Fin (axisCount n))
 (q : Row) (g : UniformJointCacheWorkspace.Geometry n axisIndex q) (k time j : ℕ)
 (slot : UniformLocalCacheChronology.Slot)
 (l : UniformForwardMatchingFactorPreparation.Layout
  (Header.forward (Cursor.shifted (context constants n axisIndex q k time) j) q slot) (envelope constants n)) :
 UniformInverseMatchingFactorPreparation.InverseLayout
  (Header.forward (Cursor.shifted (context constants n axisIndex q k time) j) q slot) l
  (UniformJointCacheWorkspace.inverse n) := by
 let c:=UniformJointCacheWorkspace.original n q
 let z:=UniformJointCacheWorkspace.stride n
 have size:=linear hn axisIndex q g
 change 100*(c.exponent+c.width+c.gates+q.a+q.e+1)+1000 ≤ z at size
 have budget:=UniformJointCacheWorkspace.ambient_budget constants n
 change 2000*z ≤ envelope constants n at budget
 constructor
 · change 31*z+6*c.gates ≤ 32*z;omega
 · change 32*z+6*c.gates ≤ envelope constants n;omega
 · omega

end
end ExactFourierCircuits.UniformCanonicalCacheSlotLayout

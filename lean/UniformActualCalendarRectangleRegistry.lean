import UniformActualCalendarRegistryFamily
import UniformActualCalendarRectangleProduced
import UniformLocalRequestGeometry
import UniformCanonicalCacheSlotGeometry

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRectangleRegistry
open UniformMachine UniformJointAllocation UniformJointCacheAllocation UniformAllAxisSeedPreparation
open UniformLocalRequestPlan UniformLocalRequestGeometry UniformLocalCacheSlotConductorMachine
open UniformActualCalendarRegistry
noncomputable section

variable {constants : Constants} {n : ℕ} {axisIndex : Fin (axisCount n)}
 {qs : List Request} {R T : ℕ} (g : Geometry constants n axisIndex qs R T)
 {s : State} (all : ∀i (hi:i<qs.length),Complete constants n axisIndex qs R T g i hi s)

def block (n : ℕ) (q : Request) : List (ℕ×ℕ):=
 List.ofFn (fun t:Fin (slotCount n q.row)=>(q.time+28*t.val,0))
def base (constants : Constants) (n : ℕ) (axisIndex : Fin (axisCount n)) : ℕ:=
 (axis constants n axisIndex).control+3*radix n axisIndex+4

def data (i : ℕ) (hi:i<qs.length) (t : ℕ) (ht:t<slotCount n qs[i].row) :=
 Classical.choice (UniformActualCalendarRectangleProduced.of_cached
  (controller constants n axisIndex qs i) qs[i].row (aBound constants n axisIndex qs i hi)
  (eBound constants n axisIndex qs i hi) (bank constants n axisIndex qs i hi)
  (g.slots i hi).positive t s (all i hi t ht))

lemma reserve_split (pool control r offset t cap:ℕ)
 (hp:pool+9*r*(offset+t)+9*r≤cap)
 (hn:control+(3*r+11)*(offset+t)+3*r+4+7≤cap):
 pool+9*r*offset+9*r*t+9*r≤cap ∧
 control+(3*r+11)*offset+3*r+4+(3*r+11)*t+7≤cap ∧
 control+(3*r+11)*offset+(3*r+11)*t+r≤cap:=by
 rw[Nat.mul_add] at hp hn
 exact ⟨by omega,by omega,by omega⟩

lemma block_get (n:ℕ)(q:Request)(t:Fin (block n q).length):
 (block n q).get t=(q.time+28*t.val,0):=by
 exact List.getElem_ofFn t.isLt

include g in
lemma bounds (hn:0<n) (i:ℕ) (hi:i<qs.length) (t:ℕ) (ht:t<slotCount n qs[i].row):
 (Cursor.shifted (controller constants n axisIndex qs i) t).pool+9*radix n axisIndex≤3*slab constants n ∧
 (Cursor.shifted (controller constants n axisIndex qs i) t).cacheDirectory+7≤3*slab constants n ∧
 (Cursor.shifted (controller constants n axisIndex qs i) t).cachePermutation+radix n axisIndex≤3*slab constants n:=by
 have next:=past_prefix n qs hi (Nat.le_refl qs.length) hi
 have cap:slotPrefix n qs i+t≤UniformJointCacheExtent.capacity (radix n axisIndex):=by
  have:=g.capacity
  omega
 have result:=UniformCanonicalCacheSlotGeometry.persistent_bounds constants hn axisIndex
  (slotPrefix n qs i+t) cap
 rw[controller,requestAt_eq qs i hi]
 change
  (axis constants n axisIndex).pool+9*radix n axisIndex*slotPrefix n qs i+9*radix n axisIndex*t+
   9*radix n axisIndex≤3*slab constants n ∧
  (axis constants n axisIndex).control+(3*radix n axisIndex+11)*slotPrefix n qs i+
   3*radix n axisIndex+4+(3*radix n axisIndex+11)*t+7≤3*slab constants n ∧
  (axis constants n axisIndex).control+(3*radix n axisIndex+11)*slotPrefix n qs i+
   (3*radix n axisIndex+11)*t+radix n axisIndex≤3*slab constants n
 change
  (axis constants n axisIndex).pool+9*radix n axisIndex*(slotPrefix n qs i+t)+9*radix n axisIndex≤3*slab constants n ∧
  (axis constants n axisIndex).control+(3*radix n axisIndex+11)*(slotPrefix n qs i+t)+3*radix n axisIndex+4+7≤3*slab constants n ∧ _ at result
 exact reserve_split _ _ _ _ _ _ result.1 result.2.1

/-- Every factory is constructed from the real rectangle-loop cache witnesses;
only ordinary arena extents remain as numerical arguments. -/
def family (hn:0<n) {O N:ℕ} (scalarRoom:3*slab constants n≤O) (natRoom:3*slab constants n≤N)
 (radixRoom:radix n axisIndex≤envelope constants n) (i:ℕ) (hi:i<qs.length):
 Family (radix n axisIndex) O N (envelope constants n)
  (base constants n axisIndex+(3*radix n axisIndex+11)*slotPrefix n qs i)
  (3*radix n axisIndex+11) (block n qs[i]) s where
 entry:=fun t=>by
  have ht:t.val<slotCount n qs[i].row:=by simpa only[block,List.length_ofFn] using t.isLt
  let d:=data g all i hi t.val ht
  have b:=bounds g hn i hi t.val ht
  have ambient:(controller constants n axisIndex qs i).ambient=radix n axisIndex:=rfl
  have kind:(controller constants n axisIndex qs i).kind=0:=rfl
  have produced:=d.produced _ _ _ _ _ _ _ _ kind (b.2.1.trans natRoom) (b.1.trans scalarRoom)
   (b.2.2.trans natRoom) radixRoom
  apply Produced.cast produced ambient
  · change (axis constants n axisIndex).control+(3*radix n axisIndex+11)*slotPrefix n qs i+
     3*radix n axisIndex+4+(3*radix n axisIndex+11)*t.val=
     base constants n axisIndex+(3*radix n axisIndex+11)*slotPrefix n qs i+(3*radix n axisIndex+11)*t.val
    unfold base
    omega
  · rw[block_get]
    rw[controller,requestAt_eq qs i hi]
    rfl
  · rw[block_get]

end
end ExactFourierCircuits.UniformActualCalendarRectangleRegistry

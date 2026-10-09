import UniformDirectLeafHighFinal
import UniformJointCacheTime
import UniformCacheTimingBounds
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestModel
open UniformLocalCacheTreeMachine UniformLocalCacheTreeExecution UniformCacheTimingWalk
open UniformJointCacheExtent UniformJointCacheTime UniformWorkspacePlanner UniformBalancedToeplitz
open UniformDirectLeafCacheLoopBoot (size)

/-- The exact branch used by the actual canonical DFS, including width zero
and one. A selected=0 test alone would omit a possible width-one leaf. -/
def leaf (q:Visit):Prop:=q.task.width<2 ∨ selected q.task.width=0
instance (q:Visit):Decidable (leaf q):=inferInstanceAs (Decidable (_ ∨ _))
def operations (q:Visit):ℕ:=if leaf q then size q.task.width else 0
def before (visits:List Visit) (i:ℕ):ℕ:=((visits.take i).map operations).sum
def demand (visits:List Visit):ℕ:=(visits.map operations).sum
lemma demand_append (xs ys:List Visit):demand (xs++ys)=demand xs+demand ys:=by
 simp only[demand,List.map_append,List.sum_append]
lemma before_zero (visits:List Visit):before visits 0=0:=rfl
lemma before_length (visits:List Visit):before visits visits.length=demand visits:=by
 simp only[before,demand,List.take_length]
lemma before_next (visits:List Visit) (i:ℕ) (hi:i<visits.length):
 before visits (i+1)=before visits i+operations visits[i]:=by
 rw[before,List.take_succ_eq_append_getElem hi]
 simp only[List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
 rfl
lemma before_le (visits:List Visit) (i:ℕ):before visits i≤demand visits:=by
 have eq:=demand_append (visits.take i) (visits.drop i)
 rw[List.take_append_drop] at eq
 change demand (visits.take i)≤demand visits
 omega
lemma numbered_demand {v:ℕ} (P:Plan v) (hp:Canonical P) (o k c parent side:ℕ):
 demand (numbered P o k c parent side)=leafOperations P:=by
 induction P generalizing o k c parent side with
 | direct v cap=>
  change v<2 ∨selected v=0 at hp
  change (if v<2 ∨selected v=0 then UniformDirectLeafCacheLoopBoot.size v else 0)=
   (UniformTransposeDescriptorMachine.leafRecords v 0 0).length
  rw[ite_eq_left hp,UniformTransposeDescriptorMachine.leafRecords_length]
  rfl
 | split v hn hv L R ihL ihR=>
  let lc:=c+7*UniformLocalRectangleDescriptors.emittedCount v
  let ls:=numbered L o (k+1) lc k 0
  let rs:=numbered R (o+v/2) (k+1+ls.length) (lc+7*visitSum ls) k 1
  simp only[numbered,demand,List.map_cons,List.sum_cons,List.map_append,List.sum_append,leafOperations]
  change operations ⟨⟨v,o,parent,side⟩,c⟩+(demand ls+demand rs)=leafOperations L+leafOperations R
  have zero:operations ⟨⟨v,o,parent,side⟩,c⟩=0:=by
   change (if v<2 ∨selected v=0 then UniformDirectLeafCacheLoopBoot.size v else 0)=0
   rw[ite_eq_right hp.1]
  rw[zero,Nat.zero_add]
  exact congrArg₂ (·+·) (ihL hp.2.1 _ _ _ _ _) (ihR hp.2.2 _ _ _ _ _)
lemma root_demand (v o R:ℕ):demand (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1=
 leafOperations (plan v):=by
 rw[root_walk_numbered]
 exact numbered_demand _ (plan_canonical v) _ _ _ _ _
lemma actual_capacity (v o R:ℕ):
 ((UniformLocalCacheTreeCoverage.visitedRows (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1).map
  (fun q=>slotCount (exponent q.a q.e))).sum+
  2*demand (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1≤capacity v:=by
 have bound:=actual_walk_slots v o R
 have leaves:=leaf_operations_bound (plan v)
 rw[root_demand]
 omega

/-- Both descriptor banks are produced afresh for every genuine leaf; the
persistent cache counts both orientations, not only the forward word. -/
def cachedBefore (rectangles:ℕ) (visits:List Visit) (i:ℕ):ℕ:=rectangles+2*before visits i
lemma cached_next (rectangles:ℕ) (visits:List Visit) (i:ℕ) (hi:i<visits.length):
 cachedBefore rectangles visits (i+1)=cachedBefore rectangles visits i+2*operations visits[i]:=by
 rw[cachedBefore,before_next _ _ hi,cachedBefore];ring
end ExactFourierCircuits.UniformDirectLeafForestModel

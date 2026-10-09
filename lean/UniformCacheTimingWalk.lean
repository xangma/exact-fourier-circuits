import UniformLocalCacheTiming
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingWalk
open UniformLocalCacheTreeMachine UniformLocalCacheTreeExecution
open UniformLocalCacheTreeCoverage UniformLocalCacheTiming
open UniformLocalRectangleDescriptors (emittedCount)
open UniformBalancedToeplitz UniformWorkspacePlanner

lemma walk_nil (fuel k c : ℕ) : walk fuel k c [] = ([],[]) := by
 cases fuel <;> rfl

/-- Resume the actual integer DFS; both counters come from its real prefix. -/
lemma walk_add (fuel extra k c : ℕ) (tasks : List Task) :
 walk (fuel+extra) k c tasks =
 let first := walk fuel k c tasks
 let last := walk extra (k+first.1.length) (c+7*visitSum first.1) first.2
 (first.1++last.1,last.2) := by
 induction fuel generalizing k c tasks with
 | zero => simp [walk,visitSum]
 | succ fuel ih =>
  cases tasks with
  | nil => simp only [walk_nil,List.length_nil,visitSum,List.map_nil,List.sum_nil,
      Nat.add_zero,Nat.mul_zero,List.nil_append]
  | cons t ts =>
   rw [show fuel+1+extra=(fuel+extra)+1 by omega]
   simp only [walk]
   rw [ih]
   simp only [List.length_cons,visitSum,List.map_cons,List.sum_cons,List.cons_append]
   simp only [Nat.mul_add,Nat.add_assoc,Nat.add_comm]

/-- The exact parent-first numbered tree, including physical request offsets. -/
def numbered : {v : ℕ} → Plan v → ℕ → ℕ → ℕ → ℕ → ℕ → List Visit
 | v,.direct _ _,o,_,c,parent,side => [⟨⟨v,o,parent,side⟩,c⟩]
 | v,.split _ _ _ L R,o,k,c,parent,side =>
   let lc := c+7*emittedCount v
   let left := numbered L o (k+1) lc k 0
   let right := numbered R (o+v/2) (k+1+left.length) (lc+7*visitSum left) k 1
   ⟨⟨v,o,parent,side⟩,c⟩ :: (left++right)

lemma numbered_length {v : ℕ} (P : Plan v) (o k c parent side : ℕ) :
 (numbered P o k c parent side).length=(ofPlan P o).nodeCount := by
 induction P generalizing o k c parent side with
 | direct => rfl
 | split v hn hv L R ihL ihR =>
  simp only [numbered,List.length_cons,List.length_append,ihL,ihR,ofPlan,Tree.nodeCount]
  omega

/-- No traversal or request-address certificate is supplied: this is the
literal DFS reference on exactly one measured canonical subtree. -/
lemma walk_numbered {v : ℕ} (P : Plan v) (hp : Canonical P)
 (o k c parent side : ℕ) (tail : List Task) :
 walk (ofPlan P o).nodeCount k c (⟨v,o,parent,side⟩::tail)=
 (numbered P o k c parent side,tail) := by
 induction P generalizing o k c parent side tail with
 | direct v cap =>
  have stop : v<2 ∨ selected v=0 := hp
  simp only [ofPlan,Tree.nodeCount,walk,children,stop,ite_true,List.nil_append,numbered]
 | split v hn hv L R ihL ihR =>
  have split : ¬(v<2 ∨ selected v=0) := by omega
  have left := ihL hp.2.1 o (k+1) (c+7*emittedCount v) k 0
    (⟨v-v/2,o+v/2,k,1⟩::tail)
  have right := ihR hp.2.2 (o+v/2)
    (k+1+(numbered L o (k+1) (c+7*emittedCount v) k 0).length)
    (c+7*emittedCount v+7*visitSum (numbered L o (k+1) (c+7*emittedCount v) k 0)) k 1 tail
  change walk (1+(ofPlan L o).nodeCount+(ofPlan R (o+v/2)).nodeCount) k c
    (⟨v,o,parent,side⟩::tail)=_
  rw [show 1+(ofPlan L o).nodeCount+(ofPlan R (o+v/2)).nodeCount=
    ((ofPlan L o).nodeCount+(ofPlan R (o+v/2)).nodeCount)+1 by omega]
  simp only [walk,children,split,ite_false,List.cons_append,List.nil_append]
  rw [walk_add,left]
  dsimp only
  rw [right]
  rfl

/-- This is the actual 173-printer's complete visit list, not an arbitrary tree
with a matching multiset of requests. -/
lemma root_walk_numbered (v o R : ℕ) :
 (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1 =
 numbered (plan v) o 0 R 0 0 := by
 let P:=plan v
 have enough : (ofPlan P o).nodeCount≤2*v+1 := by
  by_cases positive : 0<v
  · have h:=ofPlan_nodeCount_tight P o positive;omega
  · have vz:v=0:=by omega
    subst v
    simp [P,plan,ofPlan,Tree.nodeCount]
 have exactRun:=walk_numbered P (plan_canonical v) o 0 R 0 0 []
 rw [show 2*v+1=(ofPlan P o).nodeCount+(2*v+1-(ofPlan P o).nodeCount) by omega,
   walk_add,exactRun]
 simp only [walk_nil,List.append_nil]
 rfl

end ExactFourierCircuits.UniformCacheTimingWalk

import UniformCacheTimingForwardLoop
import UniformCacheTimingBottomUp
import UniformCacheTimingMetadata
import UniformCacheTimingBounds
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingForwardCanonical
open UniformMachine UniformCacheTimingControl
open UniformLocalCacheTreeMachine UniformLocalCacheTreeExecution UniformLocalCacheTreeIteration
open UniformLocalCacheTreeCoverage UniformCacheTimingReference UniformCacheTimingMetadata
open UniformCacheTimingBottomUp UniformCacheTimingBounds UniformLocalRectangleDescriptors
open UniformCacheTimingForwardLoop

def data (visits : List Visit) (k : ℕ) : Data :=
 if hk : k < visits.length then
  {parent:=visits[k].task.parent
   ordinal:=visitSum (visits.take k)
   duration:=taskDuration visits[k].task
   correction:=correction visits[k]
   prefixes:=List.ofFn (fun j : Fin (emittedCount visits[k].task.width)=>requestPrefix visits[k] j)}
 else {parent:=0,ordinal:=0,duration:=0,correction:=0,prefixes:=[]}
lemma data_eq (visits : List Visit) (k : ℕ) (hk : k < visits.length) :
 data visits k=
  {parent:=visits[k].task.parent
   ordinal:=visitSum (visits.take k)
   duration:=taskDuration visits[k].task
   correction:=correction visits[k]
   prefixes:=List.ofFn (fun j : Fin (emittedCount visits[k].task.width)=>requestPrefix visits[k] j)} := by
 simp [data,hk]

/-- These are the temporary words actually produced by the reverse machine;
none is a supplied start-time output. -/
structure Stored (U V T : ℕ) (visits : List Visit) (s : State) : Prop where
 durations : ∀k,(hk:k < visits.length)→s.natHeap (U+k)=some (bottomUp visits k)
 corrections : ∀k,(hk:k < visits.length)→s.natHeap (V+k)=some (correction visits[k])
 prefixes : ∀k,(hk:k < visits.length)→∀j,j < emittedCount visits[k].task.width→
  s.natHeap (T+visitSum (visits.take k)+j)=some (requestPrefix visits[k] j)

lemma directory_at {D start : ℕ} {visits : List Visit} {s : State}
 (h : Directory D start visits s) (k : ℕ) (hk : k < visits.length) :
 AtNode D (start+k) visits[k].task visits[k].rectangleBase s := by
 induction visits generalizing start k with
 | nil => simp at hk
 | cons q qs ih =>
  cases k with
  | zero => simpa only [List.getElem_cons_zero,Nat.add_zero] using h.1
  | succ k =>
   have hh:=ih h.2 k (by simpa using hk)
   simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

lemma bank (v o D R U V T : ℕ) (s : State)
 (directory : Directory D 0 (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1 s)
 (stored : Stored U V T (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1 s) :
 Bank D R U V T (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1.length
  (data (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1) 0 s := by
 let visits:=(walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1
 constructor
 · intro k hk
   have node:=directory_at directory k hk
   have par:=node ⟨3,by decide⟩
   have base:=node ⟨5,by decide⟩
   have count:=node ⟨6,by decide⟩
   simp only [Nat.zero_add,nodeWords,List.getElem_cons_succ,List.getElem_cons_zero] at par base count
   rw [data_eq _ k hk]
   simp only [List.length_ofFn]
   refine ⟨par,?_,count⟩
   rw [walk_rectangle_prefix] at base
   exact base
 · intro k hk
   rw [data_eq _ k hk]
   change s.natHeap (U+k)=some (taskDuration visits[k].task)
   rw [←root_bottomUp v o R k hk]
   exact stored.durations k hk
 · intro k hk
   rw [data_eq _ k hk]
   simpa only [Nat.not_lt_zero,ite_false] using stored.corrections k hk
 · intro k hk j hj
   simp only [data_eq _ k hk] at hj ⊢
   simp only [List.length_ofFn] at hj
   simpa only [Nat.not_lt_zero,ite_false,List.getElem_ofFn] using stored.prefixes k hk j hj

/-- All control and word side conditions follow from the canonical physical
traversal and its actual schedule length. -/
lemma ordered (v o R B : ℕ) (word : UniformLocalCacheTiming.planDuration (UniformBalancedToeplitz.plan v) ≤ B) :
 Ordered (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1.length
  (visitSum (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1) B (data (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1) := by
 constructor
 · intro k hk
   simp only [data_eq _ k hk]
   by_cases zero : k=0
   · exact Or.inl zero
   · exact Or.inr (root_parentBefore v o R k hk (by omega))
 · intro i j less jBound
   have iBound : i < (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1.length := by omega
   simpa only [data_eq _ i iBound,data_eq _ j jBound,List.length_ofFn] using
    visitSum_request_before (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1 i j iBound less
 · intro k hk
   simpa only [data_eq _ k hk,List.length_ofFn] using
    visitSum_request_end (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1 k hk
 · intro k hk value hv
   simp only [data_eq _ k hk] at hv ⊢
   obtain ⟨j,eq⟩:=List.mem_ofFn.mp hv
   rw [←eq]
   exact (requestStart_le _ j).trans ((root_duration_le v o R k hk).trans word)

/-- The charged forward pass applied to the real173 traversal and the actual
reverse-produced duration/correction/prefix banks. -/
theorem execution (n v o D R U V T B : ℕ) (x : Fin n→ℂ) (s : State)
 (g : Layout D U V T (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1.length
  (visitSum (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1) B)
 (word : UniformLocalCacheTiming.planDuration (UniformBalancedToeplitz.plan v) ≤ B)
 (h : Header D R U V T (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1.length
  (visitSum (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1) s)
 (directory : Directory D 0 (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1 s)
 (stored : Stored U V T (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1 s)
 (hp : s.pc=86) (hs : WordBound B s) : ∃u,
 BoundedExecution UniformCacheTimingProgram.program n x B s
  (ticks (data (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1) 0 (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1.length+2) u ∧
 (∀k,(hk:k < (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1.length)→u.natHeap (V+k)=some 0) ∧
 (∀k,(hk:k < (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1.length)→∀j,
   j < emittedCount (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1[k].task.width→
   u.natHeap (T+visitSum ((walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1.take k)+j)=
    some (requestStart (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1[k] j)) ∧
 (∀z,(z < V∨V+(walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1.length ≤ z)→
   (z < T∨T+visitSum (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1 ≤ z)→u.natHeap z=s.natHeap z) := by
 obtain ⟨u,run,up,ubank,frame⟩:=UniformCacheTimingForwardLoop.execution n D R U V T _ _ B
  (data (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1) x s g (ordered v o R B word) h (bank v o D R U V T s directory stored) hp hs
 refine ⟨u,run,?_,?_,frame⟩
 · intro k hk
   simpa only [ite_eq_left hk] using ubank.starts k hk
 · intro k hk j hj
   have value:=ubank.prefixes k hk j (by simpa only [data_eq _ k hk,List.length_ofFn] using hj)
   simpa only [data_eq _ k hk,List.getElem_ofFn,ite_eq_left hk,requestStart] using value
def rowCount (a : ℕ→Data) : ℕ→ℕ→ℕ
 | _,0=>0
 | i,fuel+1=>(a i).prefixes.length+rowCount a (i+1) fuel
lemma ticks_bound (a : ℕ→Data) (i fuel : ℕ) :
 ticks a i fuel ≤ 26*fuel+8*rowCount a i fuel+1 := by
 induction fuel generalizing i with
 | zero => simp [ticks,rowCount]
 | succ fuel ih =>
  have rest:=ih (i+1)
  simp only [ticks,rowCount,UniformCacheTimingForwardNode.ticks]
  split_ifs <;>omega
lemma rowCount_suffix (visits : List Visit) (i fuel : ℕ) (endIndex : i+fuel=visits.length) :
 rowCount (data visits) i fuel=visitSum (visits.drop i) := by
 induction fuel generalizing i with
 | zero =>
  have eq : i=visits.length := by omega
  simp [rowCount,eq,visitSum]
 | succ fuel ih =>
  have hi : i < visits.length := by omega
  rw [rowCount,data_eq _ i hi]
  simp only [List.length_ofFn]
  rw [ih (i+1) (by omega),List.drop_eq_getElem_cons hi]
  simp only [visitSum,List.map_cons,List.sum_cons]
lemma execution_ticks_bound (visits : List Visit) :
 ticks (data visits) 0 visits.length+2 ≤ 26*visits.length+8*visitSum visits+3 := by
 have h:=ticks_bound (data visits) 0 visits.length
 rw [rowCount_suffix visits 0 visits.length (by omega)] at h
 simp only [List.drop_zero] at h
 omega
end ExactFourierCircuits.UniformCacheTimingForwardCanonical

import UniformLocalRectangleDescriptors
import UniformLocalCacheChronology

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheTreeMachine
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformWorkspacePlanner
open UniformLocalRectangleDescriptors (Row row rows emittedCount)

/-- The physical tree keeps parallel children separate from the later rectangle
sequence. Its prepared-cache traversal may visit the parent first. -/
inductive Tree where
 | direct (width offset:ℕ)
 | split (width offset chunk:ℕ) (left right:Tree)
 deriving Repr, DecidableEq

def ofPlan {n:ℕ} (P:UniformBalancedToeplitz.Plan n) (o:ℕ):Tree:=
 match P with
 | .direct n _ => .direct n o
 | .split n _ _ L R=>.split n o (selected n) (ofPlan L o) (ofPlan R (o+n/2))

def Tree.nodeCount:Tree→ℕ
 | .direct _ _=>1
 | .split _ _ _ L R=>1+L.nodeCount+R.nodeCount

def Tree.rectangles:Tree→List Row
 | .direct _ _=>[]
 | .split v o b L R=>rows v o b++L.rectangles++R.rectangles

/-- Algebraic kernel coordinates deliberately omit physical subtree offset. -/
def Row.kernel (r:Row):ℕ×ℕ×ℕ×ℕ×ℕ:=(r.a,r.e,r.split,r.i0,r.j0)
def requestKernel {N:ℕ} (q:UniformLocalPreparationDAG.Request N):ℕ×ℕ×ℕ×ℕ×ℕ:=
 (q.a,q.e,q.s,q.i₀,q.j₀)

lemma ofPlan_nodeCount_tight {n:ℕ} (P:UniformBalancedToeplitz.Plan n) (o:ℕ) (hn:0<n):
 (ofPlan P o).nodeCount≤2*n-1:=by
 induction P generalizing o with
 | direct n cap=>simp [ofPlan,Tree.nodeCount];omega
 | split n big hv L R ihL ihR=>
   have hl:=ihL o (by omega :0<n/2)
   have hr:=ihR (o+n/2) (by omega :0<n-n/2)
   simp only [ofPlan,Tree.nodeCount]
   omega

/-- Parent-first physical cache preparation is a permutation of all actual
left/right/postorder requests. Only prepared-cache order changes. -/
lemma ofPlan_kernel_coverage {n N:ℕ} (P:UniformBalancedToeplitz.Plan n) (o:ℕ) (hN:n≤N):
 ((ofPlan P o).rectangles.map Row.kernel).Perm
 ((UniformLocalPreparationDAG.requests P hN).map requestKernel):=by
 induction P generalizing o with
 | direct n cap=>simp [ofPlan,Tree.rectangles,UniformLocalPreparationDAG.requests]
 | split n hn hv L R ihL ihR=>
   have hl:=ihL o (by omega:n/2≤N)
   have hr:=ihR (o+n/2) (by omega:n-n/2≤N)
   have pairs:
     (rows n o (selected n)).map Row.kernel=
     (UniformBalancedToeplitz.pairs n).map (fun q=>
       requestKernel (UniformLocalPreparationDAG.pairRequest hn hv hN q)):=by
    rw [UniformLocalRectangleDescriptors.rows_pairs]
    simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro q hq
    rfl
   simp only [ofPlan,Tree.rectangles,UniformLocalPreparationDAG.requests,List.map_append]
   rw [pairs]
   let A:=(UniformBalancedToeplitz.pairs n).map (fun q=>
     requestKernel (UniformLocalPreparationDAG.pairRequest hn hv hN q))
   simpa only [List.append_assoc,List.map_map,Function.comp_def,A] using
    (((List.Perm.refl A).append (hl.append hr)).trans List.perm_append_comm)

/-- Kernel cache contains every real request, including all ragged rectangles. -/
lemma ofPlan_request_present {n N:ℕ} (P:UniformBalancedToeplitz.Plan n) (o:ℕ) (hN:n≤N)
 (q:UniformLocalPreparationDAG.Request N) (hq:q∈UniformLocalPreparationDAG.requests P hN):
 requestKernel q∈(ofPlan P o).rectangles.map Row.kernel:=by
 rw [(ofPlan_kernel_coverage P o hN).mem_iff]
 exact List.mem_map.mpr ⟨q,hq,rfl⟩

lemma ofPlan_rectangles_length {n:ℕ} (P:UniformBalancedToeplitz.Plan n) (o:ℕ):
 (ofPlan P o).rectangles.length≤n^2:=by
 have h:((ofPlan P o).rectangles.map Row.kernel).length=
   ((UniformLocalPreparationDAG.requests P (le_refl n)).map requestKernel).length:=
  (ofPlan_kernel_coverage P o (le_refl n)).length_eq
 simp only [List.length_map] at h
 rw [h]
 exact UniformLocalPreparationDAG.requests_length P (le_refl n)

/-- The actual measured plan uses exactly the physical printer's branch. -/
def Canonical:{n:ℕ}→UniformBalancedToeplitz.Plan n→Prop
 | _,.direct n _=>n<2 ∨selected n=0
 | _,.split n _ _ L R=>¬(n<2 ∨selected n=0)∧Canonical L∧Canonical R
lemma plan_canonical (n:ℕ):Canonical (UniformBalancedToeplitz.plan n):=by
 rw [UniformBalancedToeplitz.plan]
 split
 · assumption
 · rename_i h
   exact ⟨h,plan_canonical (n/2),plan_canonical (n-n/2)⟩
termination_by n
decreasing_by all_goals omega

/-- Integer-only parallel/sequence structure. A split runs its two children in
parallel (with identity padding) before its actual rectangle replay sequence. -/
inductive Shape where
 | direct (width offset:ℕ)
 | parallel (left right:Shape)
 | rectangle (q:Row)
 | sequence (parts:List Shape)
 deriving Repr

def ofPlanShape {n:ℕ} (P:UniformBalancedToeplitz.Plan n) (o:ℕ):Shape:=
 match P with
 | .direct n _=>.direct n o
 | .split n _ _ L R=>.sequence
   (.parallel (ofPlanShape L o) (ofPlanShape R (o+n/2))::
     ((rows n o (selected n)).map Shape.rectangle))

lemma shape_split {n:ℕ} (hn:2≤n) (hv:0<selected n)
 (L:UniformBalancedToeplitz.Plan (n/2)) (R:UniformBalancedToeplitz.Plan (n-n/2)) (o:ℕ):
 ofPlanShape (.split n hn hv L R) o=.sequence
  (.parallel (ofPlanShape L o) (ofPlanShape R (o+n/2))::
    ((UniformBalancedToeplitz.pairs n).map fun q=>Shape.rectangle
      (row n o (selected n) q.1.val q.2.val))):=by
 simp only [ofPlanShape,UniformLocalRectangleDescriptors.rows_pairs,List.map_map,Function.comp_def]

/-- Stack tasks contain only integer widths/offsets and tree links. -/
structure Task where
 width:ℕ
 offset:ℕ
 parent:ℕ
 side:ℕ
 deriving DecidableEq, Repr

def Task.words(t:Task):List ℕ:=[t.width,t.offset,t.parent,t.side]
def children (t:Task) (id:ℕ):List Task:=
 if t.width<2 ∨selected t.width=0 then [] else
 [⟨t.width/2,t.offset,id,0⟩,⟨t.width-t.width/2,t.offset+t.width/2,id,1⟩]

def taskWeight (t:Task):ℕ:=if t.width=0 then 1 else 2*t.width-1
lemma taskWeight_positive(t:Task):0<taskWeight t:=by
 unfold taskWeight;split <;>omega
lemma taskWeight_root (v o:ℕ):taskWeight ⟨v,o,0,0⟩≤2*v+1:=by
 simp only [taskWeight];split <;>omega
lemma children_weight(t:Task)(k:ℕ):
 ((children t k).map taskWeight).sum<taskWeight t:=by
 unfold children
 split
 · simp only [List.map_nil,List.sum_nil];exact taskWeight_positive t
 · rename_i h
   have hw:t.width≠0:=by omega
   have left:t.width/2≠0:=by omega
   have right:t.width-t.width/2≠0:=by omega
   simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,taskWeight,
    hw,left,right,ite_false,Nat.add_zero]
   omega
lemma taskWeight_length(tasks:List Task):tasks.length≤(tasks.map taskWeight).sum:=by
 induction tasks with
 | nil=>simp
 | cons t ts ih=>simp only [List.length_cons,List.map_cons,List.sum_cons];have ht:=taskWeight_positive t;omega
lemma children_bound (t:Task) (k:ℕ) (u:Task) (hu:u∈children t k):
 u.width≤t.width∧u.offset+u.width≤t.offset+t.width∧u.parent=k∧u.side≤1:=by
 unfold children at hu
 split at hu
 · simp at hu
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
   rcases hu with rfl|rfl <;>simp <;>omega

/-- Integer-only reference for the real LIFO worklist. It is never a runtime
callback or a supplied visited-node certificate. -/
structure Visit where
 task:Task
 rectangleBase:ℕ
 deriving Repr, DecidableEq

def walk:ℕ→ℕ→ℕ→List Task→List Visit×List Task
 | 0,_,_,tasks=>([],tasks)
 | _+1,_,_,[] =>([],[])
 | fuel+1,k,c,t::ts =>
   let next:=walk fuel (k+1) (c+7*emittedCount t.width) (children t k++ts)
   (⟨t,c⟩::next.1,next.2)
lemma walk_finished (fuel k c:ℕ) (tasks:List Task)
 (enough:(tasks.map taskWeight).sum≤fuel):(walk fuel k c tasks).2=[]:=by
 induction fuel generalizing k c tasks with
 | zero=>
   cases tasks with
   | nil=>rfl
   | cons t ts=>have ht:=taskWeight_positive t;simp only [List.map_cons,List.sum_cons] at enough;omega
 | succ fuel ih=>
   cases tasks with
   | nil=>rfl
   | cons t ts=>
     have drop:=children_weight t k
     have tail:((children t k++ts).map taskWeight).sum≤fuel:=by
      simp only [List.map_append,List.sum_append,List.map_cons,List.sum_cons] at enough ⊢
      omega
     exact ih (k+1) (c+7*emittedCount t.width) (children t k++ts) tail
lemma walk_length (fuel k c:ℕ) (tasks:List Task):(walk fuel k c tasks).1.length≤fuel:=by
 induction fuel generalizing k c tasks with
 | zero=>simp [walk]
 | succ fuel ih=>
   cases tasks with
   | nil=>simp [walk]
   | cons t ts=>simp only [walk,List.length_cons];have h:=ih (k+1) (c+7*emittedCount t.width) (children t k++ts);omega

/-- Literal DFS: the right task is pushed first, then the left task. -/
def boot:List Op:=[.literal 4290 0,.literal 4291 1,.literal 4292 2,.literal 4293 4,.literal 4294 7,
 .literal 4280 1,.literal 4281 0,.add 4282 4274 4290,.add 4283 4272 4290,
 .putNat 4283 4270,.add 4283 4283 4291,.putNat 4283 4271,
 .add 4283 4283 4291,.putNat 4283 4290,.add 4283 4283 4291,.putNat 4283 4290]

def pop:List Op:=[.sub 4280 4280 4291,.mul 4283 4280 4293,.add 4283 4272 4283,
 .getNat 4240 4283,.add 4283 4283 4291,.getNat 4241 4283,
 .add 4283 4283 4291,.getNat 4287 4283,.add 4283 4283 4291,.getNat 4288 4283,
 .add 4242 4282 4290]

def emitNode:List Op:=[.mul 4283 4281 4294,.add 4283 4273 4283,
 .putNat 4283 4240,.add 4283 4283 4291,.putNat 4283 4241,
 .add 4283 4283 4291,.putNat 4283 4250,.add 4283 4283 4291,.putNat 4283 4287,
 .add 4283 4283 4291,.putNat 4283 4288,.add 4283 4283 4291,.putNat 4283 4282,
 .add 4283 4283 4291,.putNat 4283 4257,
 .add 4289 4281 4290,.add 4281 4281 4291,
 .mul 4286 4257 4294,.add 4282 4282 4286]

def push:List Op:=[.mul 4283 4280 4293,.add 4283 4272 4283,
 .putNat 4283 4252,.add 4283 4283 4291,.add 4285 4241 4251,.putNat 4283 4285,
 .add 4283 4283 4291,.putNat 4283 4289,.add 4283 4283 4291,.putNat 4283 4291,
 .add 4280 4280 4291,.mul 4283 4280 4293,.add 4283 4272 4283,
 .putNat 4283 4251,.add 4283 4283 4291,.putNat 4283 4241,
 .add 4283 4283 4291,.putNat 4283 4289,.add 4283 4283 4291,.putNat 4283 4290,
 .add 4280 4280 4291]

-- Boot16; outer16; pop17..27; node printer28..128, return129;
-- node record129..147; small branch148; positive149; push150..170;
-- back171; halt172.
def program:Program:=boot.map Op.code++[.branchLT 4290 4280 17 172]++pop.map Op.code++
 UniformLocalRectangleDescriptors.program.map (relocate 28 129)++emitNode.map Op.code++
 [.branchLT 4240 4292 171 149,.branchLT 4290 4250 150 171]++push.map Op.code++[.jump 16,.halt]
lemma program_length:program.length=173:=by
 simp only [program,List.length_append,List.length_map,UniformLocalRectangleDescriptors.program_length];rfl
lemma boot_length:boot.length=16:=rfl
lemma pop_length:pop.length=11:=rfl
lemma emit_length:emitNode.length=19:=rfl
lemma push_length:push.length=21:=rfl

end ExactFourierCircuits.UniformLocalCacheTreeMachine

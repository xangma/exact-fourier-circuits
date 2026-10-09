import UniformLocalCacheTreeIteration

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheTreeExecution
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformLocalCacheTreeMachine UniformLocalCacheTreeIteration
open UniformWorkspacePlanner
open UniformLocalRectangleDescriptors (emittedCount)

structure Layout (v o W D R B:ℕ):Prop where
 code:173≤B
 search:UniformWorkspaceSearchMachine.budget v≤B
 stack:W+4*(2*v+2)≤D
 directory:D+7*(2*v+2)≤R
 requests:R+7*(2*v+2)*v^2≤B
 native:o+v≤B
 width:2*v+173≤B

def Good (v o:ℕ) (tasks:List Task):Prop:=
 ∀t∈tasks,t.width≤v∧t.offset+t.width≤o+v
lemma Good.tail {v o:ℕ} {t:Task} {ts:List Task} (h:Good v o (t::ts)):Good v o ts:=
 fun u hu=>h u (by simp [hu])
lemma Good.children {v o:ℕ} {t:Task} {ts:List Task} (h:Good v o (t::ts)) (k:ℕ):
 Good v o (children t k++ts):=by
 intro u hu
 rcases List.mem_append.mp hu with hu|hu
 · have parent:=h t (by simp)
   have child:=children_bound t k u hu
   exact ⟨child.1.trans parent.1,child.2.1.trans parent.2⟩
 · exact h.tail u hu

lemma chunk_bound (w v:ℕ) (hw:w≤v):
 chunkCount (w-w/2) (selected w)≤v∧chunkCount (w/2) (selected w)≤v:=by
 by_cases empty:selected w=0
 · simp [empty,chunkCount]
 · have positive:0<selected w:=by omega
   have left:=UniformBalancedToeplitz.chunkCount_le (w-w/2) (selected w) positive
   have right:=UniformBalancedToeplitz.chunkCount_le (w/2) (selected w) positive
   omega
lemma pair_bound (w v:ℕ) (hw:w≤v):
 chunkCount (w-w/2) (selected w)*chunkCount (w/2) (selected w)≤v^2:=by
 have h:=chunk_bound w v hw
 simpa only [pow_two] using Nat.mul_le_mul h.1 h.2
lemma emitted_bound (w v:ℕ) (hw:w≤v):emittedCount w≤v^2:=by
 have h:=pair_bound w v hw
 unfold emittedCount;split <;>omega
lemma search_bound (w v:ℕ) (hw:w≤v):
 UniformWorkspaceSearchMachine.budget w≤UniformWorkspaceSearchMachine.budget v:=by
 have h:=Nat.pow_le_pow_left (by omega:w+1≤v+1) 2
 unfold UniformWorkspaceSearchMachine.budget
 omega

def nodeBudget (v:ℕ):ℕ:=256*(v+1)^4+(22*v+9)*v+69
lemma nodeBudget_bound (w v:ℕ) (hw:w≤v):
 256*(w+1)^4+(22*chunkCount (w/2) (selected w)+9)*chunkCount (w-w/2) (selected w)+69≤nodeBudget v:=by
 have powers:=Nat.pow_le_pow_left (by omega:w+1≤v+1) 4
 have chunks:=chunk_bound w v hw
 have h:=Nat.mul_le_mul (show 22*chunkCount (w/2) (selected w)+9≤22*v+9 by omega) chunks.1
 unfold nodeBudget
 omega

structure Invariant (v o W D R k used:ℕ) (tasks:List Task) (s:State):Prop where
 cursor:Cursor v o W D R k (R+7*used) tasks s
 stack:Stack W tasks s
 good:Good v o tasks
 capacity:k+(tasks.map taskWeight).sum≤2*v+1
 used:used≤k*v^2

lemma iteration_resources {v o W D R k used B:ℕ} {t:Task} {ts:List Task} {s:State}
 (h:Invariant v o W D R k used (t::ts) s) (layout:Layout v o W D R B):
 W+4*(ts.length+2)≤D ∧D+7*(k+1)≤R∧R≤R+7*used∧
 UniformWorkspaceSearchMachine.budget t.width≤B∧
 R+7*used+7*(chunkCount (t.width-t.width/2) (selected t.width)*chunkCount (t.width/2) (selected t.width))≤B∧
 t.offset+t.width/2≤B∧2*t.width+173≤B:=by
 have bound:=h.good t (by simp)
 have counts:=taskWeight_length (t::ts)
 have pair:=pair_bound t.width v bound.1
 have kk:k≤2*v+1:=by have hh:=h.capacity;omega
 have ls:=layout.stack
 have ld:=layout.directory
 refine ⟨?_,?_,by omega,(search_bound t.width v bound.1).trans layout.search,?_,?_,?_⟩
 · have cap:=h.capacity;simp only [List.length_cons] at counts
   have hm:=Nat.mul_le_mul_left 4 (show ts.length+2≤2*v+2 by omega)
   omega
 · have hm:=Nat.mul_le_mul_left 7 (show k+1≤2*v+2 by omega)
   omega
 · have used:=h.used
   have hm:=Nat.mul_le_mul_right (v^2) (show k+1≤2*v+2 by omega)
   have rr:=layout.requests
   nlinarith
 · have nn:=layout.native;omega
 · have ww:=layout.width;omega

lemma invariant_next {v o W D R k used:ℕ} {t:Task} {ts:List Task} {s u:State}
 (h:Invariant v o W D R k used (t::ts) s)
 (cursor:Cursor v o W D R (k+1) (R+7*used+7*emittedCount t.width) (children t k++ts) u)
 (stack:Stack W (children t k++ts) u):
 Invariant v o W D R (k+1) (used+emittedCount t.width) (children t k++ts) u:=by
 have drop:=children_weight t k
 have cb:=emitted_bound t.width v (h.good t (by simp)).1
 refine ⟨?_,stack,h.good.children k,?_,?_⟩
 · convert cursor using 1;ring
 · have cap:=h.capacity
   simp only [List.map_cons,List.sum_cons] at cap
   simp only [List.map_append,List.sum_append]
   omega
 · have used:=h.used
   rw [Nat.add_mul,Nat.one_mul]
   omega

lemma boot_code:BlockAt boot program 0:=by
 intro i hi;change i<16 at hi;interval_cases i <;>rfl
lemma boot_header {v o W D R:ℕ} (s:State) (h:Header v o W D R s):
 Cursor v o W D R 0 R [⟨v,o,0,0⟩] (applyBlock boot s):=by
 constructor
 · constructor <;>first |(simpa [boot,applyBlock,Op.apply,writeNat,next] using h.width) |
    (simpa [boot,applyBlock,Op.apply,writeNat,next] using h.offset) |
    (simpa [boot,applyBlock,Op.apply,writeNat,next] using h.stack) |
    (simpa [boot,applyBlock,Op.apply,writeNat,next] using h.directory) |
    (simpa [boot,applyBlock,Op.apply,writeNat,next] using h.requests)
 · constructor <;>simp [boot,applyBlock,Op.apply,writeNat,next]
 · simp [boot,applyBlock,Op.apply,writeNat,next]
 · simp [boot,applyBlock,Op.apply,writeNat,next]
 · simp [boot,applyBlock,Op.apply,writeNat,next,h.requests]
lemma boot_stack {v o W D R:ℕ} (s:State) (h:Header v o W D R s):
 Stack W [⟨v,o,0,0⟩] (applyBlock boot s):=by
 intro i f
 have iz:i.val=0:=by have hi:=i.isLt;simp only [List.length_singleton] at hi;omega
 fin_cases f <;>simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next,
  h.stack,h.width,h.offset,Task.words,Nat.add_assoc]
lemma boot_safe {v o W D R B:ℕ} (s:State) (h:Header v o W D R s)
 (hs:WordBound B s) (layout:Layout v o W D R B):readable boot s∧peak boot s≤B:=by
 have hv:=hs.2.1 4270
 have ho:=hs.2.1 4271
 have hr:=hs.2.1 4274
 rw [h.width] at hv
 rw [h.offset] at ho
 rw [h.requests] at hr
 constructor
 · simp [boot,readable,Op.readable]
 · simp [boot,peak,Op.peak,Op.apply,writeNat,next,h.stack,h.width,h.offset,h.requests]
   have stack:=layout.stack;have dir:=layout.directory;have request:=layout.requests;have code:=layout.code
   omega
lemma initialized {v o W D R:ℕ} (s:State) (h:Header v o W D R s):
 Invariant v o W D R 0 0 [⟨v,o,0,0⟩] (applyBlock boot s):=by
 refine ⟨?_,boot_stack s h,?_,?_,by simp⟩
 · simpa using boot_header s h
 · intro t ht;simp only [List.mem_singleton] at ht;subst t;simp
 · simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.zero_add,Nat.add_zero] using taskWeight_root v o


def visitSum(visits:List Visit):ℕ:=(visits.map fun q=>emittedCount q.task.width).sum

def Directory (D:ℕ):ℕ→List Visit→State→Prop
 | _,[],_=>True
 | k,q::qs,s=>AtNode D k q.task q.rectangleBase s∧Directory D (k+1) qs s

def RequestTables (visits:List Visit) (s:State):Prop:=
 ∀q∈visits,2≤q.task.width→0<selected q.task.width→
 UniformLocalRectangleDescriptors.Table q.task.width q.task.offset q.rectangleBase (selected q.task.width) s

lemma Directory.withPC {D k:ℕ} {visits:List Visit} {s:State}
 (h:Directory D k visits s) (pc:ℕ):Directory D k visits (setPC s pc):=by
 induction visits generalizing k with
 | nil=>trivial
 | cons q qs ih=>exact ⟨h.1,ih h.2⟩

lemma RequestTables.withPC {visits:List Visit} {s:State}
 (h:RequestTables visits s) (pc:ℕ):RequestTables visits (setPC s pc):=by
 intro q hq big positive
 exact h q hq big positive

lemma loop (n v o W D R B fuel k used:ℕ) (tasks:List Task) (x:Fin n→ℂ) (s:State)
 (layout:Layout v o W D R B) (h:Invariant v o W D R k used tasks s)
 (hp:s.pc=16) (hs:WordBound B s):
 ∃u time,BoundedRuns program n x B s time u∧time≤fuel*nodeBudget v∧u.pc=16∧
 Invariant v o W D R (k+(walk fuel k (R+7*used) tasks).1.length)
  (used+visitSum (walk fuel k (R+7*used) tasks).1) (walk fuel k (R+7*used) tasks).2 u∧
 Directory D k (walk fuel k (R+7*used) tasks).1 u∧
 RequestTables (walk fuel k (R+7*used) tasks).1 u∧
 Prior D R k (R+7*used) s u∧(∀q,q<W→u.natHeap q=s.natHeap q):=by
 induction fuel generalizing k used tasks s with
 | zero=>
   refine ⟨s,0,.refl hs,by simp,hp,?_,by trivial,?_,fun q dq pq=>rfl,fun q hq=>rfl⟩
   · simpa [walk,visitSum] using h
   · intro q hq;simp [walk] at hq
 | succ fuel ih=>
   cases tasks with
   | nil=>
     refine ⟨s,0,.refl hs,by simp,hp,?_,by trivial,?_,fun q dq pq=>rfl,fun q hq=>rfl⟩
     · simpa [walk,visitSum] using h
     · intro q hq;simp [walk] at hq
   | cons t ts=>
     have resources:=iteration_resources h layout
     obtain ⟨a,ta,first,time,ap,cursor,stack,current,node,prior,low⟩:=
      UniformLocalCacheTreeIteration.iteration n v o W D R k (R+7*used) B t ts x s
       h.cursor h.stack hp hs resources.1 resources.2.1 resources.2.2.1 resources.2.2.2.1
       resources.2.2.2.2.1 resources.2.2.2.2.2.1 resources.2.2.2.2.2.2
     have next:=invariant_next h cursor stack
     let w:=walk fuel (k+1) (R+7*(used+emittedCount t.width)) (children t k++ts)
     have we:walk (fuel+1) k (R+7*used) (t::ts)=
      (⟨t,R+7*used⟩::w.1,w.2):=by
       simp only [walk,w]
       congr 2 <;>ring
     obtain ⟨u,tu,tail,tailTime,up,final,dir,tables,past,pastLow⟩:=ih (k+1)
       (used+emittedCount t.width) (children t k++ts) a next ap first.final_bound
     have maxTime:ta≤nodeBudget v:=time.trans (nodeBudget_bound t.width v (h.good t (by simp)).1)
     refine ⟨u,ta+tu,first.trans tail,?_,up,?_,?_,?_,?_,?_⟩
     · rw [Nat.add_mul,Nat.one_mul];omega
     · rw [we]
       simpa only [List.length_cons,visitSum,List.map_cons,List.sum_cons,Nat.add_assoc,
         Nat.add_comm,Nat.add_left_comm] using final
     · rw [we]
       refine ⟨?_,dir⟩
       intro f
       rw [past _ (by omega) (Or.inl (by have hf:=f.isLt;omega))]
       exact current f
     · rw [we]
       intro q hq big positive
       rcases List.mem_cons.mp hq with rfl|hq
       · intro i j bound f
         dsimp only at big positive i j bound ⊢
         have product:emittedCount t.width=
          chunkCount (t.width-t.width/2) (selected t.width)*chunkCount (t.width/2) (selected t.width):=by
          simp [emittedCount,show ¬t.width<2 by omega,show selected t.width≠0 by omega]
         have lower:R≤R+7*used+7*(i.val*chunkCount (t.width/2) (selected t.width)+j.val)+f.val:=by omega
         have upper:R+7*used+7*(i.val*chunkCount (t.width/2) (selected t.width)+j.val)+f.val<
            R+7*(used+emittedCount t.width):=by
           rw [product,Nat.mul_add]
           have hf:=f.isLt;omega
         rw [past _ (by have ld:=layout.directory;omega) (Or.inr ⟨lower,upper⟩)]
         exact node.table big positive i j bound f
       · exact tables q hq big positive
     · intro q dq pq
       rw [past q dq (by
        rcases pq with less|⟨rq,cq⟩
        · left;omega
        · right;exact ⟨rq,by have hm:=Nat.mul_add 7 used (emittedCount t.width);omega⟩)]
       exact prior q dq pq
     · intro q hq;exact (pastLow q hq).trans (low q hq)

/-- The original entry has no stack, directory, selected-chunk, node-count or
visited-node readiness premise. Every source record is written by boot/DFS. -/
theorem execution (n v o W D R B:ℕ) (x:Fin n→ℂ) (s:State)
 (headers:Header v o W D R s) (layout:Layout v o W D R B)
 (hp:s.pc=0) (hs:WordBound B s):
 ∃u time,BoundedExecution program n x B s time u∧time≤(2*v+1)*nodeBudget v+18∧u.pc=172∧
 Directory D 0 (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1 u∧
 RequestTables (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1 u∧
 u.natReg 4281=(walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1.length∧
 u.natReg 4282=R+7*visitSum (walk (2*v+1) 0 R [⟨v,o,0,0⟩]).1∧
 (∀q,q<W→u.natHeap q=s.natHeap q):=by
 have safe:=boot_safe s headers hs layout
 have first:=block_runs boot program 0 n B x s boot_code hp hs (by rw [boot_length];have hc:=layout.code;omega)
  safe.1 safe.2
 let a:=applyBlock boot s
 have ap:a.pc=16:=by rw [applyBlock_pc,hp,boot_length]
 have init:=initialized s headers
 obtain ⟨z,tz,run,cost,zp,final,dir,tables,past,low⟩:=loop n v o W D R B (2*v+1) 0 0
   [⟨v,o,0,0⟩] x a layout init ap first.final_bound
 simp only [Nat.mul_zero,Nat.add_zero,Nat.zero_add] at final dir tables
 have empty:(walk (2*v+1) 0 R [⟨v,o,0,0⟩]).2=[]:=walk_finished _ _ _ _ (by
  simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using taskWeight_root v o)
 have pending:z.natReg 4280=0:=by simpa only [empty,List.length_nil] using final.cursor.pending
 have step:UniformMachine.step program n x z=.running (setPC z 172):=by
  simp [UniformMachine.step,zp,outer_at,pending,final.cursor.zero,setPC]
 have exit:=UniformPreparationRowTableMachine.control_run program n B 172 x z run.final_bound
  (by have hc:=layout.code;omega) step
 have halt:BoundedExecution program n x B (setPC z 172) 1 (setPC z 172):=
  .halt exit.final_bound (by simp [UniformMachine.step,setPC,finish_at])
 refine ⟨setPC z 172,16+tz+2,?_,by omega,rfl,dir.withPC 172,tables.withPC 172,?_,?_,?_⟩
 · simpa only [boot_length,Nat.add_assoc] using first.executes (run.executes (exit.executes halt))
 · simpa only [setPC] using final.cursor.processed
 · simpa only [setPC] using final.cursor.requestCursor
 · intro q hq
   exact (low q hq).trans (by
    simp (disch:=omega) [a,boot,applyBlock,Op.apply,writeNat,next,headers.stack,headers.width,headers.offset])

lemma program_natOnly:∀ins∈program,UniformLocalRectangleDescriptors.NatOnly ins:=by
 have top:program.all (fun ins=>decide (UniformLocalRectangleDescriptors.NatOnly ins))=true:=by decide
 exact fun ins hi=>of_decide_eq_true ((List.all_eq_true.mp top) ins hi)

lemma execution_scalarFrame {n B t:ℕ} {x:Fin n→ℂ} {s u:State}
 (h:BoundedExecution program n x B s t u):UniformLocalRectangleDescriptors.ScalarFrame s u:=
 UniformLocalRectangleDescriptors.natOnly_execution program_natOnly h.executes

def destinations (ins:Instruction):Prop:=match ins with
 | .natLiteral d _ | .natBinary _ d _ _ | .loadNat d _=>290≤d∧d<4295
 | _=>True
instance(ins:Instruction):Decidable (destinations ins):=by cases ins <;>simp [destinations] <;>infer_instance
lemma program_destinations:∀ins∈program,destinations ins:=by
 have top:program.all (fun ins=>decide (destinations ins))=true:=by decide
 exact fun ins hi=>of_decide_eq_true ((List.all_eq_true.mp top) ins hi)
lemma keeps_nat (q:ℕ)(hq:q<290∨4295≤q):∀ins∈program,UniformNewtonTableMachine.KeepsNat q ins:=by
 intro ins hi
 have bounds:=program_destinations ins hi
 have allowed:=program_natOnly ins hi
 cases ins <;>simp only [destinations] at bounds
 all_goals simp only [UniformLocalRectangleDescriptors.NatOnly] at allowed
 all_goals simp only [UniformNewtonTableMachine.KeepsNat]
 all_goals omega
lemma execution_natFrame {n B t:ℕ} {x:Fin n→ℂ} {s u:State}
 (h:BoundedExecution program n x B s t u)(q:ℕ)(hq:q<290∨4295≤q):u.natReg q=s.natReg q:=
 UniformNewtonTableMachine.Executes.keeps_nat h.executes (keeps_nat q hq)

end ExactFourierCircuits.UniformLocalCacheTreeExecution

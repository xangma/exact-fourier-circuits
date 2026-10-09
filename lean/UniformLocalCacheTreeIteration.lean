import UniformLocalCacheTreeMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheTreeIteration
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformLocalCacheTreeMachine
open UniformWorkspacePlanner
open UniformLocalRectangleDescriptors (emittedCount)

def Stack (W:ℕ) (tasks:List Task) (s:State):Prop:=
 ∀(i:Fin tasks.length)(f:Fin 4),s.natHeap (W+4*(tasks.length-1-i.val)+f.val)=
 some ((tasks[i.val]'i.isLt).words[f.val]'f.isLt)
lemma Stack.head {W:ℕ} {t:Task} {ts:List Task} {s:State} (h:Stack W (t::ts) s) (f:Fin 4):
 s.natHeap (W+4*ts.length+f.val)=some (t.words[f.val]'f.isLt):=by
 simpa [Task.words] using
  h ⟨0,by simp⟩ f
lemma Stack.tail {W:ℕ} {t:Task} {ts:List Task} {s:State} (h:Stack W (t::ts) s):Stack W ts s:=by
 intro i f
 have hi:=i.isLt
 have eq:(t::ts).length-1-(i.val+1)=ts.length-1-i.val:=by simp only [List.length_cons];omega
 simpa [Task.words,eq,Nat.sub_sub,Nat.add_comm] using h ⟨i.val+1,by simpa using i.isLt⟩ f

structure Constants (s:State):Prop where
 zero:s.natReg 4290=0
 one:s.natReg 4291=1
 two:s.natReg 4292=2
 four:s.natReg 4293=4
 seven:s.natReg 4294=7
structure Header (v o W D R:ℕ) (s:State):Prop where
 width:s.natReg 4270=v
 offset:s.natReg 4271=o
 stack:s.natReg 4272=W
 directory:s.natReg 4273=D
 requests:s.natReg 4274=R
structure Cursor (v o W D R k cursor:ℕ) (tasks:List Task) (s:State):Prop
 extends Header v o W D R s, Constants s where
 pending:s.natReg 4280=tasks.length
 processed:s.natReg 4281=k
 requestCursor:s.natReg 4282=cursor

lemma pop_code:BlockAt pop program 17:=by
 intro i hi;change i<11 at hi;interval_cases i <;>rfl
lemma emit_code:BlockAt emitNode program 129:=by
 intro i hi;change i<19 at hi;interval_cases i <;>rfl
lemma push_code:BlockAt push program 150:=by
 intro i hi;change i<21 at hi;interval_cases i <;>rfl
lemma node_code:CodeAt UniformLocalRectangleDescriptors.program program 28 129:=by
 let before:=boot.map Op.code++[.branchLT 4290 4280 17 172]++pop.map Op.code
 let after:=emitNode.map Op.code++[.branchLT 4240 4292 171 149,.branchLT 4290 4250 150 171]++
  push.map Op.code++[.jump 16,.halt]
 have length:before.length=28:=by simp only [before,List.length_append,List.length_map,boot_length,pop_length];rfl
 have eq:program=before++UniformLocalRectangleDescriptors.program.map (relocate 28 129)++after:=by
  simp only [program,before,after,List.append_assoc]
 rw [eq]
 intro i hi
 rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map,length];omega)]
 rw [List.getElem?_append_right (by rw [length];omega)]
 simp only [length,show 28+i-28=i by omega,List.getElem?_map]

noncomputable section
lemma pop_result {v o W D R k c:ℕ} {t:Task} {ts:List Task}
 (s:State) (h:Cursor v o W D R k c (t::ts) s) (stack:Stack W (t::ts) s):
 UniformLocalRectangleDescriptors.Header t.width t.offset c (applyBlock pop s)∧
 (applyBlock pop s).natReg 4280=ts.length∧
 (applyBlock pop s).natReg 4287=t.parent∧(applyBlock pop s).natReg 4288=t.side:=by
 have h0:=stack.head ⟨0,by decide⟩
 have h1:=stack.head ⟨1,by decide⟩
 have h2:=stack.head ⟨2,by decide⟩
 have h3:=stack.head ⟨3,by decide⟩
 simp [Task.words,Nat.mul_comm,Nat.add_assoc] at h0 h1 h2 h3
 refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
 all_goals simp [pop,applyBlock,Op.apply,writeNat,next,h.pending,h.stack,h.requestCursor,
   h.one,h.zero,h.four,Nat.add_assoc,h0,h1,h2,h3]

lemma pop_heap (s:State):(applyBlock pop s).natHeap=s.natHeap:=rfl
lemma pop_keeps (s:State) (q:ℕ) (hq:4264≤q) (h0:q≠4280) (h1:q≠4283)
 (h2:q≠4287) (h3:q≠4288):(applyBlock pop s).natReg q=s.natReg q:=by
 simp [pop,applyBlock,Op.apply,writeNat,next,show q≠4240 by omega,show q≠4241 by omega,
  show q≠4242 by omega,h0,h1,h2,h3]

lemma pop_safe {v o W D R k c B:ℕ} {t:Task} {ts:List Task}
 (s:State) (h:Cursor v o W D R k c (t::ts) s) (stack:Stack W (t::ts) s)
 (hs:WordBound B s) (endStack:W+4*(ts.length+1)≤B):
 readable pop s∧peak pop s≤B:=by
 have h0:=stack.head ⟨0,by decide⟩
 have h1:=stack.head ⟨1,by decide⟩
 have h2:=stack.head ⟨2,by decide⟩
 have h3:=stack.head ⟨3,by decide⟩
 simp [Task.words,Nat.mul_comm,Nat.add_assoc] at h0 h1 h2 h3
 have a0:=hs.2.2.1 _ _ h0
 have a1:=hs.2.2.1 _ _ h1
 have a2:=hs.2.2.1 _ _ h2
 have a3:=hs.2.2.1 _ _ h3
 have cc:=hs.2.1 4282
 rw [h.requestCursor] at cc
 constructor
 · simp [pop,readable,Op.readable,Op.apply,writeNat,next,h.pending,h.stack,
    h.one,h.four,Nat.add_assoc,h0,h1,h2,h3]
 · simp [pop,peak,Op.peak,Op.apply,writeNat,next,h.pending,h.stack,h.requestCursor,
    h.one,h.zero,h.four,Nat.add_assoc,h0,h1,h2,h3]
   omega

/-- The producer itself supplies selected b, all row reads, and count. The caller
state is the real pop→Search58→printer state, not a supplied prepared boundary. -/
lemma selected_node (n v o W D R k c B:ℕ) (t:Task) (ts:List Task)
 (x:Fin n→ℂ) (s:State) (h:Cursor v o W D R k c (t::ts) s)
 (stack:Stack W (t::ts) s) (hp:s.pc=17) (hs:WordBound B s)
 (endStack:W+4*(ts.length+1)≤B)
 (search:UniformWorkspaceSearchMachine.budget t.width≤B)
 (rows:c+7*(chunkCount (t.width-t.width/2) (selected t.width)*chunkCount (t.width/2) (selected t.width))≤B)
 (offset:t.offset≤B) (width:2*t.width+173≤B):
 ∃u time,BoundedRuns program n x B s time u∧
 time≤256*(t.width+1)^4+(22*chunkCount (t.width/2) (selected t.width)+9)*
   chunkCount (t.width-t.width/2) (selected t.width)+25∧u.pc=129∧
 UniformLocalRectangleDescriptors.Result t.width t.offset c u∧
 UniformLocalRectangleDescriptors.Outside c
  (chunkCount (t.width-t.width/2) (selected t.width)*chunkCount (t.width/2) (selected t.width)) s u∧
 (∀q,4264≤q→q≠4280→q≠4283→q≠4287→q≠4288→u.natReg q=s.natReg q)∧
 u.natReg 4280=ts.length∧u.natReg 4287=t.parent∧u.natReg 4288=t.side:=by
 have safe:=pop_safe s h stack hs endStack
 have first:=block_runs pop program 17 n B x s pop_code hp hs (by rw [pop_length];omega) safe.1 safe.2
 let a:=applyBlock pop s
 have ap:a.pc=28:=by rw [applyBlock_pc,hp,pop_length]
 have fields:=pop_result s h stack
 let entry:=setPC a 0
 have eb:WordBound B entry:=changePC_bound B a 0 first.final_bound (by omega)
 have eh:UniformLocalRectangleDescriptors.Header t.width t.offset c entry:=
  ⟨fields.1.width,fields.1.offset,fields.1.destination⟩
 obtain ⟨u,ticks,run,cost,up,result,outside⟩:=UniformLocalRectangleDescriptors.execution
  n t.width t.offset c B x entry eh rfl eb search rows offset (by omega)
 have placed:=UniformBoundedAssembly.boundedExecution_placed node_code
  (by rw [UniformLocalRectangleDescriptors.program_length];omega) (by omega) run
 have eq:UniformAssembly.placed 28 entry=a:=by
  change {a with pc:=28+0}=a
  rw [←ap];cases a;rfl
 rw [eq] at placed
 let final:=setPC u 129
 have retained(q:ℕ)(hq:4264≤q):final.natReg q=a.natReg q:=
  UniformLocalRectangleDescriptors.execution_high_nat run q hq
 refine ⟨final,11+ticks,first.trans placed,by omega,rfl,?_,?_,?_,?_,?_,?_⟩
 · exact ⟨result.toBase.withPC 129,result.count,result.table⟩
 · intro q hq;exact (outside q hq).trans (congrFun (pop_heap s) q)
 · intro q hq n0 n1 n2 n3
   exact (retained q hq).trans (pop_keeps s q hq n0 n1 n2 n3)
 · rw [retained 4280 (by omega)];exact fields.2.1
 · rw [retained 4287 (by omega)];exact fields.2.2.1
 · rw [retained 4288 (by omega)];exact fields.2.2.2


structure Node (t:Task) (c:ℕ) (s:State):Prop extends
 UniformLocalRectangleDescriptors.Result t.width t.offset c s where
 parent:s.natReg 4287=t.parent
 side:s.natReg 4288=t.side

def nodeWords (t:Task) (c:ℕ):List ℕ:=[t.width,t.offset,selected t.width,t.parent,t.side,c,emittedCount t.width]
lemma emit_words {v o W D R k c:ℕ} {t:Task} {ts:List Task}
 (s:State) (h:Cursor v o W D R k c ts s) (node:Node t c s) (f:Fin 7):
 (applyBlock emitNode s).natHeap (D+7*k+f.val)=some ((nodeWords t c)[f.val]'f.isLt):=by
 fin_cases f <;>simp (disch:=omega) [emitNode,applyBlock,Op.apply,writeNat,next,
  h.directory,h.processed,h.requestCursor,h.one,h.seven,node.width,node.offset,node.selected,
  node.parent,node.side,node.count,nodeWords,Nat.mul_comm,Nat.add_assoc]
lemma emit_outside {v o W D R k c:ℕ} {t:Task} {ts:List Task}
 (s:State) (h:Cursor v o W D R k c ts s) (_node:Node t c s) (q:ℕ)
 (outside:q<D+7*k ∨D+7*k+7≤q):
 (applyBlock emitNode s).natHeap q=s.natHeap q:=by
 simp (disch:=omega) [emitNode,applyBlock,Op.apply,writeNat,next,
  h.directory,h.processed,h.one,h.seven]
lemma emit_result {v o W D R k c:ℕ} {t:Task} {ts:List Task}
 (s:State) (h:Cursor v o W D R k c ts s) (node:Node t c s) (disjoint:D+7*k+7≤c):
 Cursor v o W D R (k+1) (c+7*emittedCount t.width) ts (applyBlock emitNode s)∧
 (applyBlock emitNode s).natReg 4289=k∧Node t c (applyBlock emitNode s):=by
 refine ⟨?_,?_,?_⟩
 · constructor
   · constructor <;>simp [emitNode,applyBlock,Op.apply,writeNat,next,
      h.width,h.offset,h.stack,h.directory,h.requests]
   · constructor <;>simp [emitNode,applyBlock,Op.apply,writeNat,next,
      h.zero,h.one,h.two,h.four,h.seven]
   · simpa [emitNode,applyBlock,Op.apply,writeNat,next] using h.pending
   · simp [emitNode,applyBlock,Op.apply,writeNat,next,h.processed,h.one]
   · simp [emitNode,applyBlock,Op.apply,writeNat,next,h.requestCursor,node.count,h.seven,Nat.mul_comm]
 · simp [emitNode,applyBlock,Op.apply,writeNat,next,h.processed,h.zero]
 · constructor
   · constructor
     · constructor
       · exact ⟨by simpa [emitNode,applyBlock,Op.apply,writeNat,next] using node.width,
           by simpa [emitNode,applyBlock,Op.apply,writeNat,next] using node.offset,
           by simpa [emitNode,applyBlock,Op.apply,writeNat,next] using node.destination⟩
       all_goals first | (simpa [emitNode,applyBlock,Op.apply,writeNat,next] using node.selected) |
         (simpa [emitNode,applyBlock,Op.apply,writeNat,next] using node.half) |
         (simpa [emitNode,applyBlock,Op.apply,writeNat,next] using node.target) |
         (simpa [emitNode,applyBlock,Op.apply,writeNat,next] using node.zero) |
         (simpa [emitNode,applyBlock,Op.apply,writeNat,next] using node.one) |
         (simpa [emitNode,applyBlock,Op.apply,writeNat,next] using node.two) |
         (simpa [emitNode,applyBlock,Op.apply,writeNat,next] using node.seven)
     · simpa [emitNode,applyBlock,Op.apply,writeNat,next] using node.count
     · intro big positive i j bound f
       have previous:=node.table big positive i j bound f
       rw [emit_outside s h node _ (Or.inr (by have hf:=f.isLt;omega))]
       exact previous
   · simpa [emitNode,applyBlock,Op.apply,writeNat,next] using node.parent
   · simpa [emitNode,applyBlock,Op.apply,writeNat,next] using node.side


lemma emit_safe {v o W D R k c B:ℕ} {t:Task} {ts:List Task}
 (s:State) (h:Cursor v o W D R k c ts s) (node:Node t c s)
 (hs:WordBound B s) (hd:D+7*(k+1)≤B) (hc:c+7*emittedCount t.width≤B):
 readable emitNode s∧peak emitNode s≤B:=by
 have width:=hs.2.1 4240
 have offset:=hs.2.1 4241
 have sel:=hs.2.1 4250
 have parent:=hs.2.1 4287
 have side:=hs.2.1 4288
 rw [node.width] at width
 rw [node.offset] at offset
 rw [node.selected] at sel
 rw [node.parent] at parent
 rw [node.side] at side
 constructor
 · simp [emitNode,readable,Op.readable]
 · simp [emitNode,peak,Op.peak,Op.apply,writeNat,next,h.directory,h.processed,h.requestCursor,
    h.one,h.zero,h.seven,node.width,node.offset,node.selected,node.parent,node.side,node.count]
   omega


def leftTask (t:Task) (k:ℕ):Task:=⟨t.width/2,t.offset,k,0⟩
def rightTask (t:Task) (k:ℕ):Task:=⟨t.width-t.width/2,t.offset+t.width/2,k,1⟩
lemma push_left {v o W D R k c oldc:ℕ} {t:Task} {ts:List Task}
 (s:State) (h:Cursor v o W D R (k+1) c ts s) (node:Node t oldc s)
 (parent:s.natReg 4289=k) (f:Fin 4):
 (applyBlock push s).natHeap (W+4*(ts.length+1)+f.val)=
 some ((leftTask t k).words[f.val]'f.isLt):=by
 fin_cases f <;>simp (disch:=omega) [push,applyBlock,Op.apply,writeNat,next,
  h.stack,h.pending,h.one,h.zero,h.four,node.half,node.offset,parent,
  Task.words,leftTask,Nat.mul_comm,Nat.add_assoc]
lemma push_right {v o W D R k c oldc:ℕ} {t:Task} {ts:List Task}
 (s:State) (h:Cursor v o W D R (k+1) c ts s) (node:Node t oldc s)
 (parent:s.natReg 4289=k) (f:Fin 4):
 (applyBlock push s).natHeap (W+4*ts.length+f.val)=
 some ((rightTask t k).words[f.val]'f.isLt):=by
 fin_cases f <;>simp (disch:=omega) [push,applyBlock,Op.apply,writeNat,next,
  h.stack,h.pending,h.one,h.zero,h.four,node.half,node.target,node.offset,parent,
  Task.words,rightTask,Nat.mul_comm,Nat.add_assoc]
lemma push_outside {v o W D R k c:ℕ} {ts:List Task}
 (s:State) (h:Cursor v o W D R k c ts s) (q:ℕ)
 (outside:q<W+4*ts.length ∨W+4*ts.length+8≤q):
 (applyBlock push s).natHeap q=s.natHeap q:=by
 simp (disch:=omega) [push,applyBlock,Op.apply,writeNat,next,
  h.stack,h.pending,h.one,h.four]
lemma push_cursor {v o W D R k c p:ℕ} {t:Task} {ts:List Task}
 (s:State) (h:Cursor v o W D R k c ts s):
 Cursor v o W D R k c (leftTask t p::rightTask t p::ts) (applyBlock push s):=by
 constructor
 · exact ⟨by simpa [push,applyBlock,Op.apply,writeNat,next] using h.width,
      by simpa [push,applyBlock,Op.apply,writeNat,next] using h.offset,
      by simpa [push,applyBlock,Op.apply,writeNat,next] using h.stack,
      by simpa [push,applyBlock,Op.apply,writeNat,next] using h.directory,
      by simpa [push,applyBlock,Op.apply,writeNat,next] using h.requests⟩
 · constructor <;>first |(simpa [push,applyBlock,Op.apply,writeNat,next] using h.zero) |
    (simpa [push,applyBlock,Op.apply,writeNat,next] using h.one) |
    (simpa [push,applyBlock,Op.apply,writeNat,next] using h.two) |
    (simpa [push,applyBlock,Op.apply,writeNat,next] using h.four) |
    (simpa [push,applyBlock,Op.apply,writeNat,next] using h.seven)
 · simp [push,applyBlock,Op.apply,writeNat,next,h.pending,h.one,Nat.add_assoc]
 · simpa [push,applyBlock,Op.apply,writeNat,next] using h.processed
 · simpa [push,applyBlock,Op.apply,writeNat,next] using h.requestCursor
lemma push_stack {v o W D R k c oldc:ℕ} {t:Task} {ts:List Task}
 (s:State) (h:Cursor v o W D R (k+1) c ts s) (node:Node t oldc s)
 (parent:s.natReg 4289=k) (stack:Stack W ts s):
 Stack W (leftTask t k::rightTask t k::ts) (applyBlock push s):=by
 intro i f
 refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun a=>?_) j) i
 · simpa [Task.words,leftTask] using push_left s h node parent f
 · simpa [Task.words,rightTask] using push_right s h node parent f
 · have he:ts.length+1+1-1-(a.val+1+1)=ts.length-1-a.val:=by omega
   have cell:W+4*(ts.length-1-a.val)+f.val<W+4*ts.length:=by
    have hf:=f.isLt;have ha:=a.isLt;omega
   simp only [Fin.val_succ,List.length_cons,he,List.getElem_cons_succ]
   rw [push_outside s h _ (Or.inl cell)]
   exact stack a f


lemma Cursor.withPC {v o W D R k c:ℕ} {tasks:List Task} {s:State}
 (h:Cursor v o W D R k c tasks s) (pc:ℕ):Cursor v o W D R k c tasks (setPC s pc):=by
 rcases h with ⟨⟨width,offset,stack,directory,requests⟩,⟨zero,one,two,four,seven⟩,pending,processed,cursor⟩
 exact ⟨⟨width,offset,stack,directory,requests⟩,⟨zero,one,two,four,seven⟩,pending,processed,cursor⟩
lemma Node.withPC {t:Task} {c:ℕ} {s:State} (h:Node t c s) (pc:ℕ):Node t c (setPC s pc):=
 ⟨⟨h.toBase.withPC pc,h.count,h.table⟩,h.parent,h.side⟩
lemma Stack.withPC {W:ℕ} {tasks:List Task} {s:State} (h:Stack W tasks s) (pc:ℕ):Stack W tasks (setPC s pc):=h

lemma push_safe {v o W D R k c oldc B:ℕ} {t:Task} {ts:List Task}
 (s:State) (h:Cursor v o W D R (k+1) c ts s) (node:Node t oldc s)
 (parent:s.natReg 4289=k) (hs:WordBound B s)
 (endStack:W+4*(ts.length+2)≤B) (offset:t.offset+t.width/2≤B):
 readable push s∧peak push s≤B:=by
 have left:=hs.2.1 4251
 have right:=hs.2.1 4252
 have hp:=hs.2.1 4289
 rw [node.half] at left
 rw [node.target] at right
 rw [parent] at hp
 constructor
 · simp [push,readable,Op.readable]
 · simp [push,peak,Op.peak,Op.apply,writeNat,next,h.stack,h.pending,h.one,h.zero,h.four,
    node.half,node.target,node.offset,parent]
   omega

lemma small_branch:program[148]?=some (.branchLT 4240 4292 171 149):=rfl
lemma positive_branch:program[149]?=some (.branchLT 4290 4250 150 171):=rfl
lemma back_at:program[171]?=some (.jump 16):=rfl
lemma finish_at:program[172]?=some .halt:=rfl
lemma outer_at:program[16]?=some (.branchLT 4290 4280 17 172):=rfl

lemma push_preserves_node {v o W D R k c oldc:ℕ} {t:Task} {ts:List Task}
 (s:State) (h:Cursor v o W D R k c ts s) (node:Node t oldc s)
 (disjoint:W+4*ts.length+8≤oldc):Node t oldc (applyBlock push s):=by
 constructor
 · constructor
   · constructor
     · exact ⟨by simpa [push,applyBlock,Op.apply,writeNat,next] using node.width,
        by simpa [push,applyBlock,Op.apply,writeNat,next] using node.offset,
        by simpa [push,applyBlock,Op.apply,writeNat,next] using node.destination⟩
     all_goals first |(simpa [push,applyBlock,Op.apply,writeNat,next] using node.selected) |
       (simpa [push,applyBlock,Op.apply,writeNat,next] using node.half) |
       (simpa [push,applyBlock,Op.apply,writeNat,next] using node.target) |
       (simpa [push,applyBlock,Op.apply,writeNat,next] using node.zero) |
       (simpa [push,applyBlock,Op.apply,writeNat,next] using node.one) |
       (simpa [push,applyBlock,Op.apply,writeNat,next] using node.two) |
       (simpa [push,applyBlock,Op.apply,writeNat,next] using node.seven)
   · simpa [push,applyBlock,Op.apply,writeNat,next] using node.count
   · intro big positive i j bound f
     rw [push_outside s h _ (Or.inr (by have hf:=f.isLt;omega))]
     exact node.table big positive i j bound f
 · simpa [push,applyBlock,Op.apply,writeNat,next] using node.parent
 · simpa [push,applyBlock,Op.apply,writeNat,next] using node.side

/-- Actual conditional stack expansion. The selected b and width came from the
charged node printer, and every stored task retains the original subtree offset. -/
lemma expand (n v o W D R k c oldc B:ℕ) (t:Task) (ts:List Task) (x:Fin n→ℂ) (s:State)
 (h:Cursor v o W D R (k+1) c ts s) (node:Node t oldc s)
 (stack:Stack W ts s) (parent:s.natReg 4289=k) (hp:s.pc=148) (hs:WordBound B s)
 (endStack:W+4*(ts.length+2)≤B) (offset:t.offset+t.width/2≤B)
 (disjoint:W+4*ts.length+8≤oldc) (code:173≤B):
 ∃u time,BoundedRuns program n x B s time u∧time≤24∧u.pc=16∧
 Cursor v o W D R (k+1) c (children t k++ts) u∧Stack W (children t k++ts) u∧Node t oldc u∧
 (∀q,(q<W ∨W+4*ts.length+8≤q)→u.natHeap q=s.natHeap q):=by
 by_cases small:t.width<2
 · have step:UniformMachine.step program n x s=.running (setPC s 171):=by
    simp [UniformMachine.step,hp,small_branch,node.width,h.two,setPC,small]
   have first:=UniformPreparationRowTableMachine.control_run program n B 171 x s hs (by omega) step
   have back:UniformMachine.step program n x (setPC s 171)=.running (setPC s 16):=by
    simp [UniformMachine.step,setPC,back_at]
   have next:=UniformPreparationRowTableMachine.control_run program n B 16 x (setPC s 171)
    first.final_bound (by omega) back
   refine ⟨setPC s 16,2,by simpa only [setPC] using first.trans next,by omega,rfl,?_,?_,node.withPC 16,fun q hq=>rfl⟩
   · simpa [children,small] using h.withPC 16
   · simpa [children,small] using stack.withPC 16
 · have step:UniformMachine.step program n x s=.running (setPC s 149):=by
    simp [UniformMachine.step,hp,small_branch,node.width,h.two,setPC,small]
   have first:=UniformPreparationRowTableMachine.control_run program n B 149 x s hs (by omega) step
   let a:=setPC s 149
   have ac:=h.withPC 149
   by_cases empty:selected t.width=0
   · have test:UniformMachine.step program n x a=.running (setPC a 171):=by
      simp [UniformMachine.step,a,positive_branch,h.zero,node.selected,setPC,empty]
     have second:=UniformPreparationRowTableMachine.control_run program n B 171 x a first.final_bound (by omega) test
     have back:UniformMachine.step program n x (setPC a 171)=.running (setPC a 16):=by
      simp [UniformMachine.step,setPC,back_at]
     have last:=UniformPreparationRowTableMachine.control_run program n B 16 x (setPC a 171)
      second.final_bound (by omega) back
     refine ⟨setPC a 16,3,by simpa only [setPC] using (first.trans second).trans last,
      by omega,rfl,?_,?_,node.withPC 16,fun q hq=>rfl⟩
     · simpa [children,empty,setPC,a] using h.withPC 16
     · simpa [children,empty,setPC,a] using stack.withPC 16
   · have positive:0<selected t.width:=by omega
     have test:UniformMachine.step program n x a=.running (setPC a 150):=by
      simp [UniformMachine.step,a,positive_branch,h.zero,node.selected,setPC,positive]
     have second:=UniformPreparationRowTableMachine.control_run program n B 150 x a first.final_bound (by omega) test
     let e:=setPC a 150
     have ec:=h.withPC 150
     have en:=node.withPC 150
     have safe:=push_safe e ec en parent second.final_bound endStack offset
     have run:=block_runs push program 150 n B x e push_code rfl second.final_bound
      (by rw [push_length];omega) safe.1 safe.2
     let f:=applyBlock push e
     have fp:f.pc=171:=by rw [applyBlock_pc];rfl
     have fc:=push_cursor (t:=t) (p:=k) e ec
     have fs:=push_stack e ec en parent stack
     have fn:=push_preserves_node e ec en disjoint
     have back:UniformMachine.step program n x f=.running (setPC f 16):=by simp [UniformMachine.step,fp,back_at,setPC]
     have last:=UniformPreparationRowTableMachine.control_run program n B 16 x f run.final_bound (by omega) back
     refine ⟨setPC f 16,24,?_,by omega,rfl,?_,?_,fn.withPC 16,?_⟩
     · simpa only [push_length,setPC,show 1+1+21+1=24 from rfl] using ((first.trans second).trans run).trans last
     · simpa [children,small,empty,leftTask,rightTask] using fc.withPC 16
     · simpa [children,small,empty,leftTask,rightTask] using fs.withPC 16
     · intro q hq;exact push_outside e ec q (by rcases hq with hq|hq;left;omega;exact Or.inr hq)


def AtNode (D k:ℕ) (t:Task) (c:ℕ) (s:State):Prop:=
 ∀f:Fin 7,s.natHeap (D+7*k+f.val)=some ((nodeWords t c)[f.val]'f.isLt)

def Prior (D R k c:ℕ) (s u:State):Prop:=
 ∀q,D≤q→(q<D+7*k ∨(R≤q∧q<c))→u.natHeap q=s.natHeap q

/-- One real fixed-program worklist iteration, including native stack reads,
selected chunk search, all ragged rectangle writes, tree links and child pushes. -/
theorem iteration (n v o W D R k c B:ℕ) (t:Task) (ts:List Task) (x:Fin n→ℂ) (s:State)
 (h:Cursor v o W D R k c (t::ts) s) (stack:Stack W (t::ts) s)
 (hp:s.pc=16) (hs:WordBound B s)
 (endStack:W+4*(ts.length+2)≤D) (dirEnd:D+7*(k+1)≤R) (requestStart:R≤c)
 (search:UniformWorkspaceSearchMachine.budget t.width≤B)
 (rows:c+7*(chunkCount (t.width-t.width/2) (selected t.width)*chunkCount (t.width/2) (selected t.width))≤B)
 (offset:t.offset+t.width/2≤B) (width:2*t.width+173≤B):
 ∃u time,BoundedRuns program n x B s time u∧
 time≤256*(t.width+1)^4+(22*chunkCount (t.width/2) (selected t.width)+9)*
   chunkCount (t.width-t.width/2) (selected t.width)+69∧u.pc=16∧
 Cursor v o W D R (k+1) (c+7*emittedCount t.width) (children t k++ts) u∧
 Stack W (children t k++ts) u∧AtNode D k t c u∧Node t c u∧Prior D R k c s u∧
 (∀q,q<W→u.natHeap q=s.natHeap q):=by
 have code:173≤B:=by omega
 have dBound:D≤B:=by omega
 have head:UniformMachine.step program n x s=.running (setPC s 17):=by
  simp [UniformMachine.step,hp,outer_at,h.zero,h.pending,setPC]
 have first:=UniformPreparationRowTableMachine.control_run program n B 17 x s hs (by omega) head
 let a:=setPC s 17
 obtain ⟨u,tu,run,cost,up,result,outside,retained,pending,parent,side⟩:=
  selected_node n v o W D R k c B t ts x a (h.withPC 17) (stack.withPC 17) rfl
   first.final_bound (by omega) search rows (by omega) width
 have reg(q:ℕ)(hq:4264≤q)(ne0:q≠4280)(ne1:q≠4283)(ne2:q≠4287)(ne3:q≠4288):
  u.natReg q=s.natReg q:=retained q hq ne0 ne1 ne2 ne3
 have cursor:Cursor v o W D R k c ts u:=by
  constructor
  · constructor
    · exact (reg 4270 (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.width
    · exact (reg 4271 (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.offset
    · exact (reg 4272 (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.stack
    · exact (reg 4273 (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.directory
    · exact (reg 4274 (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.requests
  · constructor
    · exact (reg 4290 (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.zero
    · exact (reg 4291 (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.one
    · exact (reg 4292 (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.two
    · exact (reg 4293 (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.four
    · exact (reg 4294 (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.seven
  · exact pending
  · exact (reg 4281 (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.processed
  · exact (reg 4282 (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.requestCursor
 have node:Node t c u:=⟨result,parent,side⟩
 have topStack:Stack W (t::ts) u:=by
  intro i f
  rw [outside _ (Or.inl (by have hi:=i.isLt;have hf:=f.isLt;simp only [List.length_cons] at hi ⊢;omega))]
  exact stack i f
 have smallStack:Stack W ts u:=topStack.tail
 have countBound:emittedCount t.width≤
   chunkCount (t.width-t.width/2) (selected t.width)*chunkCount (t.width/2) (selected t.width):=by
  unfold emittedCount;split <;>omega
 have safe:=emit_safe u cursor node run.final_bound (by omega) (by have hm:=Nat.mul_le_mul_left 7 countBound;omega)
 have emitRun:=block_runs emitNode program 129 n B x u emit_code up run.final_bound
  (by rw [emit_length];omega) safe.1 safe.2
 let e:=applyBlock emitNode u
 have ep:e.pc=148:=by rw [applyBlock_pc,up,emit_length]
 have after:=emit_result u cursor node (by omega)
 have remaining:Stack W ts e:=by
  intro i f
  rw [emit_outside u cursor node _ (Or.inl (by have hi:=i.isLt;have hf:=f.isLt;omega))]
  exact smallStack i f
 obtain ⟨z,tz,finish,time,zp,zc,zs,zn,high⟩:=expand n v o W D R k
  (c+7*emittedCount t.width) c B t ts x e after.1 after.2.2 remaining after.2.1 ep
   emitRun.final_bound (by omega) offset (by omega) code
 refine ⟨z,1+tu+19+tz,?_,by omega,zp,zc,zs,?_,zn,?_,?_⟩
 · simpa only [emit_length] using ((first.trans run).trans emitRun).trans finish
 · intro f
   rw [high _ (Or.inr (by have hf:=f.isLt;omega))]
   exact emit_words u cursor node f
 · intro q dq pq
   rw [high q (Or.inr (by omega))]
   rw [emit_outside u cursor node q (by
    rcases pq with less|⟨rq,cq⟩
    · exact Or.inl less
    · right;omega)]
   exact outside q (Or.inl (by rcases pq with less|⟨rq,cq⟩ <;>omega))
 · intro q hq
   rw [high q (Or.inl hq),emit_outside u cursor node q (Or.inl (by omega))]
   exact outside q (Or.inl (by omega))

end
end ExactFourierCircuits.UniformLocalCacheTreeIteration

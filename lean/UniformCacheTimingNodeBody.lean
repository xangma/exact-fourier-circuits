import UniformCacheTimingNodeStore
import UniformCacheTimingPrefix
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingNodeBody
open UniformMachine UniformAssembly UniformCacheTimingProgram UniformCacheTimingControl
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformPreparationRowTableMachine (control_run)
open UniformLocalCacheTreeMachine (Visit)
open UniformLocalCacheTreeCoverage (currentRows)
open UniformLocalRectangleDescriptors (emittedCount)
open UniformWorkspacePlanner (selected)
open UniformCacheTimingNodeRead (NodeCursor)
open UniformCacheTimingRows (amounts writePrefixes TableAt)

def value (q:Visit)(child:ℕ):ℕ:=if q.task.width<2∨selected q.task.width=0 then
 UniformLocalCacheTiming.directDuration q.task.width else child+amounts (currentRows q.task)

noncomputable section
lemma direct_cursor {D R U V T N K k child:ℕ}{q:Visit}(s:State)
 (h:NodeCursor D R U V T N K k q child s):
 UniformCacheTimingNodeStore.Cursor D R U V T N K k q.task.parent
 (UniformLocalCacheTiming.directDuration q.task.width) 0 (applyBlock direct s):=by
 constructor
 · constructor
   · constructor <;>simp [direct,applyBlock,Op.apply,writeNat,next,h.nodes,h.requests,h.durations,
     h.starts,h.requestStarts,h.rootStart,h.nodeCount,h.requestCount,h.zero,h.one,h.two,h.three,h.seven,h.fourteen]
   · simp [direct,applyBlock,Op.apply,writeNat,next,h.index]
 · simp [direct,applyBlock,Op.apply,writeNat,next,h.parent]
 · simp [direct,applyBlock,Op.apply,writeNat,next,h.durationAddress]
 · simp [direct,applyBlock,Op.apply,writeNat,next,h.startAddress]
 · simp [direct,applyBlock,Op.apply,writeNat,next,h.width,h.one,h.fourteen,UniformLocalCacheTiming.directDuration,
   Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
 · simp [direct,applyBlock,Op.apply,writeNat,next,h.correction]

lemma split_cursor {D R U V T N K k child c ordinal count:ℕ}{q:Visit}{s u:State}
 (h:NodeCursor D R U V T N K k q child s)
 (out:UniformCacheTimingRows.Cursor D R U V T N K q.rectangleBase (emittedCount q.task.width) ordinal count c u)
 (keeps:∀r,r<6528∨6551<r→u.natReg r=s.natReg r):
 UniformCacheTimingNodeStore.Cursor D R U V T N K k q.task.parent (child+c) c (applyBlock split u):=by
 have index:u.natReg 6516=k:=(keeps _ (by omega)).trans h.index
 have parent:u.natReg 6521=q.task.parent:=(keeps _ (by omega)).trans h.parent
 have daddr:u.natReg 6524=U+k:=(keeps _ (by omega)).trans h.durationAddress
 have saddr:u.natReg 6525=V+k:=(keeps _ (by omega)).trans h.startAddress
 have childValue:u.natReg 6527=child:=(keeps _ (by omega)).trans h.child
 constructor
 · constructor
   · constructor <;>simp [split,applyBlock,Op.apply,writeNat,next,out.nodes,out.requests,out.durations,
     out.starts,out.requestStarts,out.rootStart,out.nodeCount,out.requestCount,out.zero,out.one,out.two,out.three,out.seven,out.fourteen]
   · simp [split,applyBlock,Op.apply,writeNat,next,index]
 · simp [split,applyBlock,Op.apply,writeNat,next,parent]
 · simp [split,applyBlock,Op.apply,writeNat,next,daddr]
 · simp [split,applyBlock,Op.apply,writeNat,next,saddr]
 · simp [split,applyBlock,Op.apply,writeNat,next,childValue,out.correction]
 · simp [split,applyBlock,Op.apply,writeNat,next,out.correction]

/-- The actual selected/direct branches determine whether stored rectangle
records are traversed; both branches produce their own duration and correction. -/
theorem execution (n D R U V T N K k child B:ℕ)(q:Visit)(x:Fin n→ℂ)(s:State)
 (h:NodeCursor D R U V T N K k q child s)(ht:TableAt q.rectangleBase 0 (currentRows q.task) s)
 (hp:s.pc=39)(hs:WordBound B s)(code:122≤B)
 (source:q.rectangleBase+7*emittedCount q.task.width+4≤T)
 (sourceBound:q.rectangleBase+7*emittedCount q.task.width+4≤B)
 (destination:T+(q.rectangleBase-R)/7+(currentRows q.task).length≤B)
 (durationBound:value q child≤B)(correctionBound:amounts (currentRows q.task)≤B)
 (budgets:∀a∈currentRows q.task,UniformCacheRowDurationMachine.budget a.a a.e≤B):∃t u,
 BoundedRuns program n x B s t u∧t≤UniformCacheTimingRows.ticks (currentRows q.task)+6∧u.pc=78∧
 UniformCacheTimingNodeStore.Cursor D R U V T N K k q.task.parent (value q child)
 (amounts (currentRows q.task)) u∧u.natHeap=writePrefixes T ((q.rectangleBase-R)/7) 0 (currentRows q.task) s.natHeap:=by
 by_cases small:q.task.width<2
 · have leaf:currentRows q.task=[]:=by simp [currentRows,small]
   have vp:value q child=UniformLocalCacheTiming.directDuration q.task.width:=by simp [value,small]
   have step:UniformMachine.step program n x s=.running (setPC s 72):=by
    simp [UniformMachine.step,hp,code_39,h.width,h.two,small,setPC]
   have enter:=control_run program n B 72 x s hs (by omega) step
   let a:=setPC s 72
   have ah:NodeCursor D R U V T N K k q child a:=h.pc 72
   have width:q.task.width≤B:=by have hh:=hs.2.1 6519; rw [h.width] at hh; exact hh
   have directBound:UniformLocalCacheTiming.directDuration q.task.width≤B:=by rwa [vp] at durationBound
   have product:q.task.width*(q.task.width-1)≤B:=by unfold UniformLocalCacheTiming.directDuration at directBound;nlinarith
   have run:=block_runs direct program 72 n B x a direct_code rfl enter.final_bound
    (by change 76≤B;omega) (by simp [direct,readable,Op.readable]) (by
     simp [direct,peak,Op.peak,Op.apply,writeNat,next,ah.width,ah.one,ah.fourteen,Nat.mul_assoc]
     unfold UniformLocalCacheTiming.directDuration at directBound
     simp only [Nat.mul_comm,Nat.mul_left_comm] at directBound product
     omega)
   let b:=applyBlock direct a
   have bp:b.pc=76:=by rw [applyBlock_pc];rfl
   have backStep:UniformMachine.step program n x b=.running (setPC b 78):=by simp [UniformMachine.step,bp,code_76,setPC]
   have back:=control_run program n B 78 x b run.final_bound (by omega) backStep
   refine ⟨6,setPC b 78,?_,?_,rfl,?_,?_⟩
   · simpa only [show direct.length=4 from rfl,setPC] using (enter.trans run).trans back
   · simp [leaf,UniformCacheTimingRows.ticks]
   · simpa only [vp,leaf,amounts,List.map_nil,List.sum_nil] using (direct_cursor a ah).pc 78
   · simp only [leaf,writePrefixes]
     rfl
 · have step:UniformMachine.step program n x s=.running (setPC s 40):=by
    simp [UniformMachine.step,hp,code_39,h.width,h.two,small,setPC]
   have enter:=control_run program n B 40 x s hs (by omega) step
   let a:=setPC s 40
   have ah:NodeCursor D R U V T N K k q child a:=h.pc 40
   by_cases zero:selected q.task.width=0
   · have leaf:currentRows q.task=[]:=by simp [currentRows,zero]
     have vp:value q child=UniformLocalCacheTiming.directDuration q.task.width:=by simp [value,zero]
     have step2:UniformMachine.step program n x a=.running (setPC a 72):=by
      simp [UniformMachine.step,show a.pc=40 from rfl,code_40,ah.zero,ah.selected,zero,setPC]
     have enter2:=control_run program n B 72 x a enter.final_bound (by omega) step2
     let b:=setPC a 72
     have bh:NodeCursor D R U V T N K k q child b:=ah.pc 72
     have width:q.task.width≤B:=by have hh:=hs.2.1 6519; rw [h.width] at hh; exact hh
     have directBound:UniformLocalCacheTiming.directDuration q.task.width≤B:=by rwa [vp] at durationBound
     have product:q.task.width*(q.task.width-1)≤B:=by unfold UniformLocalCacheTiming.directDuration at directBound;nlinarith
     have run:=block_runs direct program 72 n B x b direct_code rfl enter2.final_bound
      (by change 76≤B;omega) (by simp [direct,readable,Op.readable]) (by
       simp [direct,peak,Op.peak,Op.apply,writeNat,next,bh.width,bh.one,bh.fourteen,Nat.mul_assoc]
       unfold UniformLocalCacheTiming.directDuration at directBound
       simp only [Nat.mul_comm,Nat.mul_left_comm] at directBound product
       omega)
     let c:=applyBlock direct b
     have cp:c.pc=76:=by rw [applyBlock_pc];rfl
     have backStep:UniformMachine.step program n x c=.running (setPC c 78):=by simp [UniformMachine.step,cp,code_76,setPC]
     have back:=control_run program n B 78 x c run.final_bound (by omega) backStep
     refine ⟨7,setPC c 78,?_,?_,rfl,?_,?_⟩
     · simpa only [show direct.length=4 from rfl,setPC] using ((enter.trans enter2).trans run).trans back
     · simp [leaf,UniformCacheTimingRows.ticks]
     · simpa only [vp,leaf,amounts,List.map_nil,List.sum_nil] using (direct_cursor b bh).pc 78
     · simp only [leaf,writePrefixes]
       rfl
   · have active:0<selected q.task.width:=by omega
     have vp:value q child=child+amounts (currentRows q.task):=by simp [value,small,zero]
     have step2:UniformMachine.step program n x a=.running (setPC a 41):=by
      simp [UniformMachine.step,show a.pc=40 from rfl,code_40,ah.zero,ah.selected,active,setPC]
     have enter2:=control_run program n B 41 x a enter.final_bound (by omega) step2
     let b:=setPC a 41
     have bh:NodeCursor D R U V T N K k q child b:=ah.pc 41
     obtain ⟨c,rows,cp,ch,heap,keeps⟩:=UniformCacheTimingRows.loop n D R U V T N K q.rectangleBase
      (emittedCount q.task.width) ((q.rectangleBase-R)/7) 0 0 B (currentRows q.task) x b bh.rows ht
      (by simpa using UniformLocalCacheTreeCoverage.currentRows_length q.task) rfl enter2.final_bound code source sourceBound
      destination (by simpa using correctionBound) budgets
     have last:=block_runs split program 77 n B x c split_code cp rows.final_bound
      (by change 78≤B;omega) (by simp [split,readable,Op.readable]) (by
       simp [split,peak,Op.peak,show c.natReg 6527=child from (keeps _ (by omega)).trans bh.child,ch.correction]
       rw [vp] at durationBound
       simpa using durationBound)
     let u:=applyBlock split c
     have up:u.pc=78:=by rw [applyBlock_pc,cp];rfl
     refine ⟨2+UniformCacheTimingRows.ticks (currentRows q.task)+1,u,?_,by omega,up,?_,heap⟩
     · simpa only [show split.length=1 from rfl,Nat.add_assoc,Nat.reduceAdd] using ((enter.trans enter2).trans rows).trans last
     · simpa only [vp,Nat.zero_add] using split_cursor bh ch keeps
end
end ExactFourierCircuits.UniformCacheTimingNodeBody

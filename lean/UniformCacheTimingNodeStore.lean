import UniformCacheTimingNodeRead
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingNodeStore
open UniformMachine UniformAssembly UniformCacheTimingProgram UniformCacheTimingControl
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformPreparationRowTableMachine (control_run)

structure Cursor (D R U V T N K k parent value correction:ℕ)(s:State):Prop extends Init D R U V T N K k s where
 parent:s.natReg 6521=parent
 durationAddress:s.natReg 6524=U+k
 startAddress:s.natReg 6525=V+k
 value:s.natReg 6526=value
 correction:s.natReg 6528=correction

def ticks (k old value:ℕ):ℕ:=if k=0 then 3 else if old<value then 8 else 6

def outputHeap (U V k parent value correction old:ℕ)(heap:ℕ→Option ℕ):ℕ→Option ℕ:=
 let next:=Function.update (Function.update heap (U+k) (some value)) (V+k) (some correction)
 if k=0 then next else Function.update next (U+parent) (some (max old value))

noncomputable section
lemma Cursor.pc {D R U V T N K k parent value correction:ℕ}{s:State}
 (h:Cursor D R U V T N K k parent value correction s)(p:ℕ):
 Cursor D R U V T N K k parent value correction (setPC s p):=
 ⟨h.toInit.pc p,h.parent,h.durationAddress,h.startAddress,h.value,h.correction⟩
lemma Cursor.reg_congr {D R U V T N K k parent value correction:ℕ}{s u:State}
 (h:Cursor D R U V T N K k parent value correction s)(same:u.natReg=s.natReg):
 Cursor D R U V T N K k parent value correction u:=by
 constructor
 · constructor
   · constructor
     · simpa only [same] using h.nodes
     · simpa only [same] using h.requests
     · simpa only [same] using h.durations
     · simpa only [same] using h.starts
     · simpa only [same] using h.requestStarts
     · simpa only [same] using h.rootStart
     · simpa only [same] using h.nodeCount
     · simpa only [same] using h.requestCount
     · simpa only [same] using h.zero
     · simpa only [same] using h.one
     · simpa only [same] using h.two
     · simpa only [same] using h.three
     · simpa only [same] using h.seven
     · simpa only [same] using h.fourteen
   · simpa only [same] using h.index
 · simpa only [same] using h.parent
 · simpa only [same] using h.durationAddress
 · simpa only [same] using h.startAddress
 · simpa only [same] using h.value
 · simpa only [same] using h.correction
lemma store_cursor {D R U V T N K k parent value correction:ℕ}(s:State)
 (h:Cursor D R U V T N K k parent value correction s):
 Cursor D R U V T N K k parent value correction (applyBlock storeDuration s):=h.reg_congr rfl
lemma store_heap {D R U V T N K k parent value correction:ℕ}(s:State)
 (h:Cursor D R U V T N K k parent value correction s):
 (applyBlock storeDuration s).natHeap=
 Function.update (Function.update s.natHeap (U+k) (some value)) (V+k) (some correction):=by
 simp [storeDuration,applyBlock,Op.apply,next,h.durationAddress,h.startAddress,h.value,h.correction]
lemma parent_cursor {D R U V T N K k parent value correction:ℕ}(s:State)
 (h:Cursor D R U V T N K k parent value correction s):
 Cursor D R U V T N K k parent value correction (applyBlock parentRead s):=by
 constructor
 · constructor
   · constructor <;>simp [parentRead,applyBlock,Op.apply,writeNat,next,h.nodes,h.requests,h.durations,
     h.starts,h.requestStarts,h.rootStart,h.nodeCount,h.requestCount,h.zero,h.one,h.two,h.three,h.seven,h.fourteen]
   · simp [parentRead,applyBlock,Op.apply,writeNat,next,h.index]
 all_goals simp [parentRead,applyBlock,Op.apply,writeNat,next,h.parent,h.durationAddress,h.startAddress,h.value,h.correction]
lemma parentWrite_cursor {D R U V T N K k parent value correction:ℕ}(s:State)
 (h:Cursor D R U V T N K k parent value correction s):
 Cursor D R U V T N K k parent value correction (applyBlock parentWrite s):=h.reg_congr rfl

/-- Completed child durations are propagated by an actual comparison and
conditional physical store. The propagated operation is max, not addition. -/
theorem execution (n D R U V T N K k parent value correction old B:ℕ)(x:Fin n→ℂ)(s:State)
 (h:Cursor D R U V T N K k parent value correction s)(hp:s.pc=78)(hs:WordBound B s)
 (code:122≤B)(durations:U+k≤B)(starts:V+k≤B)(separate:U+k<V)
 (valueBound:value≤B)(correctionBound:correction≤B)
 (parentBefore:k=0∨parent<k)(parentValue:s.natHeap (U+parent)=some old):∃u,
 BoundedRuns program n x B s (ticks k old value) u∧u.pc=19∧
 Init D R U V T N K k u∧u.natHeap=outputHeap U V k parent value correction old s.natHeap∧
 (∀r,r<6535∨6536<r→u.natReg r=s.natReg r):=by
 have first:=block_runs storeDuration program 78 n B x s storeDuration_code hp hs
  (by change 80≤B;omega) (by simp [storeDuration,readable,Op.readable]) (by
   simp [storeDuration,peak,Op.peak,Op.apply,next,h.durationAddress,h.startAddress,h.value,h.correction]
   omega)
 let a:=applyBlock storeDuration s
 have ap:a.pc=80:=by rw [applyBlock_pc,hp];rfl
 have ah:Cursor D R U V T N K k parent value correction a:=store_cursor s h
 have aheap:=store_heap s h
 by_cases zero:k=0
 · have step:UniformMachine.step program n x a=.running (setPC a 19):=by
    simp [UniformMachine.step,ap,code_80,ah.zero,ah.index,zero,setPC]
   have stop:=control_run program n B 19 x a first.final_bound (by omega) step
   refine ⟨setPC a 19,?_,rfl,ah.toInit.pc 19,?_,fun _ _=>rfl⟩
   · simpa only [ticks,ite_eq_left zero,show storeDuration.length=2 from rfl,setPC] using first.trans stop
   · simpa only [outputHeap,ite_eq_left zero,setPC] using aheap
 · have earlier:parent<k:=by omega
   have storedParent:a.natHeap (U+parent)=some old:=by
    rw [aheap]
    simp (disch:=omega) [parentValue]
   have branch:UniformMachine.step program n x a=.running (setPC a 81):=by
    simp [UniformMachine.step,ap,code_80,ah.zero,ah.index,show 0<k by omega,setPC]
   have entered:=control_run program n B 81 x a first.final_bound (by omega) branch
   let b:=setPC a 81
   have bh:Cursor D R U V T N K k parent value correction b:=ah.pc 81
   have read:=block_runs parentRead program 81 n B x b parentRead_code rfl entered.final_bound
    (by change 83≤B;omega) (by
     simp [parentRead,readable,Op.readable,Op.apply,writeNat,next,bh.durations,bh.parent,show b.natHeap=a.natHeap from rfl,storedParent]) (by
     simp [parentRead,peak,Op.peak,Op.apply,writeNat,next,bh.durations,bh.parent,show b.natHeap=a.natHeap from rfl,storedParent]
     have bound:=first.final_bound.2.2.1 _ _ storedParent
     omega)
   let c:=applyBlock parentRead b
   have cp:c.pc=83:=by rw [applyBlock_pc];rfl
   have ch:Cursor D R U V T N K k parent value correction c:=parent_cursor b bh
   have cold:c.natReg 6536=old:=by
    simp [c,parentRead,applyBlock,Op.apply,writeNat,next,bh.durations,bh.parent,show b.natHeap=a.natHeap from rfl,storedParent]
   have caddr:c.natReg 6535=U+parent:=by simp [c,parentRead,applyBlock,Op.apply,writeNat,next,bh.durations,bh.parent]
   by_cases larger:old<value
   · have step:UniformMachine.step program n x c=.running (setPC c 84):=by
      simp [UniformMachine.step,cp,code_83,cold,ch.value,larger,setPC]
     have jump:=control_run program n B 84 x c read.final_bound (by omega) step
     let d:=setPC c 84
     have dh:Cursor D R U V T N K k parent value correction d:=ch.pc 84
     have write:=block_runs parentWrite program 84 n B x d parentWrite_code rfl jump.final_bound
      (by change 85≤B;omega) (by simp [parentWrite,readable,Op.readable]) (by
       simp [parentWrite,peak,Op.peak,show d.natReg 6535=c.natReg 6535 from rfl,show d.natReg 6526=c.natReg 6526 from rfl,caddr,ch.value]
       omega)
     let e:=applyBlock parentWrite d
     have ep:e.pc=85:=by rw [applyBlock_pc];rfl
     have backstep:UniformMachine.step program n x e=.running (setPC e 19):=by
      simp [UniformMachine.step,ep,code_85,setPC]
     have back:=control_run program n B 19 x e write.final_bound (by omega) backstep
     refine ⟨setPC e 19,?_,rfl,(parentWrite_cursor d dh).toInit.pc 19,?_,?_⟩
     · simpa only [ticks,ite_eq_right zero,ite_eq_left larger,show storeDuration.length=2 from rfl,
        show parentRead.length=2 from rfl,show parentWrite.length=1 from rfl,setPC] using
        (((first.trans entered).trans read).trans jump).trans (write.trans back)
     · change Function.update a.natHeap (c.natReg 6535) (some (c.natReg 6526))=_
       rw [caddr,ch.value,aheap]
       simp [outputHeap,zero,Nat.max_eq_right (by omega:old≤value)]
     · intro r hr
       simp (disch:=omega) [e,parentWrite,d,setPC,c,parentRead,b,a,storeDuration,applyBlock,Op.apply,writeNat,next]
   · have step:UniformMachine.step program n x c=.running (setPC c 19):=by
      simp [UniformMachine.step,cp,code_83,cold,ch.value,larger,setPC]
     have back:=control_run program n B 19 x c read.final_bound (by omega) step
     refine ⟨setPC c 19,?_,rfl,ch.toInit.pc 19,?_,?_⟩
     · simpa only [ticks,ite_eq_right zero,ite_eq_right larger,show storeDuration.length=2 from rfl,
        show parentRead.length=2 from rfl,setPC] using ((first.trans entered).trans read).trans back
     · change a.natHeap=_
       unfold outputHeap
       simp only [ite_eq_right zero,←aheap,Nat.max_eq_left (by omega:value≤old)]
       exact (Function.update_eq_self_iff.mpr storedParent.symm).symm
     · intro r hr
       simp (disch:=omega) [setPC,c,parentRead,b,a,storeDuration,applyBlock,Op.apply,writeNat,next]
end
end ExactFourierCircuits.UniformCacheTimingNodeStore

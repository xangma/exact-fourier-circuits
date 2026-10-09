import UniformCacheTimingStartup
import UniformCacheTimingRows
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingNodeRead
open UniformMachine UniformAssembly UniformCacheTimingProgram UniformCacheTimingControl
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformPreparationRowTableMachine (control_run)
open UniformLocalCacheTreeMachine (Visit)
open UniformLocalCacheTreeIteration (AtNode nodeWords)
open UniformWorkspacePlanner (selected)
open UniformLocalRectangleDescriptors (emittedCount)

structure NodeCursor (D R U V T N K k:ℕ)(q:Visit)(child:ℕ)(s:State):Prop extends Header D R U V T N K s where
 index:s.natReg 6516=k
 width:s.natReg 6519=q.task.width
 selected:s.natReg 6520=selected q.task.width
 parent:s.natReg 6521=q.task.parent
 base:s.natReg 6522=q.rectangleBase
 count:s.natReg 6523=emittedCount q.task.width
 durationAddress:s.natReg 6524=U+k
 startAddress:s.natReg 6525=V+k
 child:s.natReg 6527=child
 correction:s.natReg 6528=0
 ordinal:s.natReg 6529=(q.rectangleBase-R)/7
 row:s.natReg 6530=0

noncomputable section
lemma NodeCursor.pc {D R U V T N K k child:ℕ}{q:Visit}{s:State}
 (h:NodeCursor D R U V T N K k q child s)(p:ℕ):NodeCursor D R U V T N K k q child (setPC s p):=
 ⟨h.toHeader.pc p,h.index,h.width,h.selected,h.parent,h.base,h.count,h.durationAddress,
 h.startAddress,h.child,h.correction,h.ordinal,h.row⟩
lemma NodeCursor.rows {D R U V T N K k child:ℕ}{q:Visit}{s:State}
 (h:NodeCursor D R U V T N K k q child s):
 UniformCacheTimingRows.Cursor D R U V T N K q.rectangleBase (emittedCount q.task.width)
 ((q.rectangleBase-R)/7) 0 0 s:=⟨h.toHeader,h.base,h.count,h.correction,h.ordinal,h.row⟩

def readState (R _k:ℕ)(q:Visit)(s:State):State:=
 applyBlock rowSetup (writeNat (applyBlock loadReverse (setPC s 20)) 6529 ((q.rectangleBase-R)/7))

lemma node_values {D k:ℕ}{q:Visit}{s:State}(h:AtNode D k q.task q.rectangleBase s):
 s.natHeap (D+7*k)=some q.task.width ∧
 s.natHeap (D+7*k+2)=some (selected q.task.width) ∧
 s.natHeap (D+7*k+3)=some q.task.parent ∧
 s.natHeap (D+7*k+5)=some q.rectangleBase ∧
 s.natHeap (D+7*k+6)=some (emittedCount q.task.width):=by
 have h0:=h ⟨0,by decide⟩
 have h2:=h ⟨2,by decide⟩
 have h3:=h ⟨3,by decide⟩
 have h5:=h ⟨5,by decide⟩
 have h6:=h ⟨6,by decide⟩
 simp only [nodeWords,List.getElem_cons_zero,List.getElem_cons_succ,Nat.add_zero] at h0 h2 h3 h5 h6
 exact ⟨h0,h2,h3,h5,h6⟩
lemma read_cursor {D R U V T N K k child:ℕ}(q:Visit)(s:State)
 (h:Init D R U V T N K (k+1) s)(node:AtNode D k q.task q.rectangleBase s)
 (dur:s.natHeap (U+k)=some child):NodeCursor D R U V T N K k q child (readState R k q s):=by
 have facts:=node_values node
 simp only [Nat.mul_comm,Nat.add_assoc] at facts
 constructor
 · constructor <;>simp [readState,rowSetup,loadReverse,applyBlock,Op.apply,writeNat,next,setPC,
   h.nodes,h.requests,h.durations,h.starts,h.requestStarts,h.rootStart,h.nodeCount,h.requestCount,
   h.zero,h.one,h.two,h.three,h.seven,h.fourteen]
 all_goals simp [readState,rowSetup,loadReverse,applyBlock,Op.apply,writeNat,next,setPC,
  h.nodes,h.requests,h.durations,h.starts,
  h.one,h.two,h.seven,h.index,Nat.add_assoc,facts.1,facts.2.1,
  facts.2.2.1,facts.2.2.2.1,facts.2.2.2.2,dur]
lemma read_heap (R k:ℕ)(q:Visit)(s:State):(readState R k q s).natHeap=s.natHeap:=rfl

/-- The reverse pass reads the physical seven-word directory and initialized
child accumulator; its request ordinal is computed by one charged division. -/
theorem execution (n D R U V T N K k child B:ℕ)(q:Visit)(x:Fin n→ℂ)(s:State)
 (h:Init D R U V T N K (k+1) s)(node:AtNode D k q.task q.rectangleBase s)
 (dur:s.natHeap (U+k)=some child)(hp:s.pc=19)(hs:WordBound B s)(code:122≤B)
 (directory:D+7*(k+1)≤B)(durations:U+k≤B)(starts:V+k≤B):
 BoundedRuns program n x B s 20 (readState R k q s) ∧(readState R k q s).pc=39∧
 NodeCursor D R U V T N K k q child (readState R k q s):=by
 have step:UniformMachine.step program n x s=.running (setPC s 20):=by
  simp [UniformMachine.step,hp,code_19,h.zero,h.index,setPC]
 have enter:=control_run program n B 20 x s hs (by omega) step
 let a:=setPC s 20
 have facts:=node_values node
 have bv:=hs.2.2.1 _ _ facts.1
 have bs:=hs.2.2.1 _ _ facts.2.1
 have bp:=hs.2.2.1 _ _ facts.2.2.1
 have br:=hs.2.2.1 _ _ facts.2.2.2.1
 have bc:=hs.2.2.1 _ _ facts.2.2.2.2
 have bd:=hs.2.2.1 _ _ dur
 simp only [Nat.mul_comm,Nat.add_assoc] at facts
 have read:=block_runs loadReverse program 20 n B x a loadReverse_code rfl enter.final_bound
  (by change 37≤B;omega) (by
   simp [loadReverse,readable,Op.readable,Op.apply,writeNat,next,a,setPC,h.index,h.nodes,h.durations,
    h.one,h.two,h.seven,Nat.add_assoc,facts.1,facts.2.1,facts.2.2.1,
    facts.2.2.2.1,facts.2.2.2.2,dur]) (by
   simp [loadReverse,peak,Op.peak,Op.apply,writeNat,next,a,setPC,h.index,h.nodes,h.durations,
    h.starts,h.one,h.two,h.seven,h.requests,Nat.add_assoc,facts.1,facts.2.1,facts.2.2.1,
    facts.2.2.2.1,facts.2.2.2.2,dur]
   omega)
 let b:=applyBlock loadReverse a
 have bpc:b.pc=37:=by rw [applyBlock_pc];rfl
 have numerator:b.natReg 6529=q.rectangleBase-R:=by
  simp [b,loadReverse,applyBlock,Op.apply,writeNat,next,a,setPC,h.index,h.nodes,h.durations,
   h.starts,h.one,h.two,h.seven,h.requests,Nat.add_assoc,facts.1,facts.2.1,facts.2.2.1,
   facts.2.2.2.1,facts.2.2.2.2,dur]
 have seven:b.natReg 6514=7:=by simp [b,loadReverse,applyBlock,Op.apply,writeNat,next,a,setPC,h.seven]
 let c:=writeNat b 6529 ((q.rectangleBase-R)/7)
 have divide:UniformMachine.step program n x b=.running c:=by
  simp [UniformMachine.step,bpc,code_37,evalNat,numerator,seven,c]
 have cb:=writeNat_bound B b 6529 ((q.rectangleBase-R)/7) read.final_bound
  (by omega) ((Nat.div_le_self _ _).trans (by omega))
 have divrun:BoundedRuns program n x B b 1 c:=.next read.final_bound divide (.refl cb)
 have cp:c.pc=38:=by simp [c,writeNat,next,bpc]
 have setup:=block_runs rowSetup program 38 n B x c rowSetup_code cp divrun.final_bound
  (by change 39≤B;omega) (by simp [rowSetup,readable,Op.readable]) (by simp [rowSetup,peak,Op.peak])
 refine ⟨?_,?_,read_cursor q s h node dur⟩
 · simpa only [readState,a,b,c,show loadReverse.length=17 from rfl,show rowSetup.length=1 from rfl] using ((enter.trans read).trans divrun).trans setup
 · change (applyBlock rowSetup c).pc=39
   rw [applyBlock_pc,cp]
   rfl
end
end ExactFourierCircuits.UniformCacheTimingNodeRead

import UniformDirectLeafForestForward
import UniformDirectLeafHighFrames
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestControl
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafForestData
open UniformLocalCacheTreeMachine
noncomputable section
structure Control(p:Parameters)(visits:List Visit)(i:ℕ)(s:State):Prop where
 nodes:s.natReg 6660=p.nodes
 count:s.natReg 6661=visits.length
 index:s.natReg 6662=i
 pointer:s.natReg 6663=p.nodes+7*i
 starts:s.natReg 6664=p.starts
 durations:s.natReg 6665=p.durations
 root:s.natReg 6666=p.rootDuration
 one:s.natReg 6669=1
 two:s.natReg 6670=2
 seven:s.natReg 6671=7
 four:s.natReg 6672=4
 fourteen:s.natReg 6673=14
 zero:s.natReg 6679=0
 ordinal:s.natReg 6680=p.rectangles+UniformDirectLeafForestModel.before visits i
 divisor:s.natReg 6681=9*p.radix
 forward:s.natReg 5602=p.forward
 transpose:s.natReg 5603=p.transpose
 ranges:s.natReg 6693=p.ranges
def registers:List ℕ:= [6660,6661,6662,6663,6664,6665,6666,6669,6670,6671,6672,6673,6679,6680,6681,5602,5603,6693]
lemma ofCursor {p:Parameters}{visits:List Visit}{i:ℕ}{s:State}
 (h:Cursor p visits i s):Control p visits i s:=
 ⟨h.nodes,h.count,h.index,h.pointer,h.starts,h.durations,h.root,h.one,h.two,h.seven,h.four,h.fourteen,h.zero,h.ordinal,h.divisor,h.forward,h.transpose,h.ranges⟩
lemma transport {p:Parameters}{visits:List Visit}{i:ℕ}{s u:State}
 (h:Control p visits i s)(keep:∀j∈registers,u.natReg j=s.natReg j):Control p visits i u:=by
 constructor
 · exact (keep 6660 (by decide)).trans h.nodes
 · exact (keep 6661 (by decide)).trans h.count
 · exact (keep 6662 (by decide)).trans h.index
 · exact (keep 6663 (by decide)).trans h.pointer
 · exact (keep 6664 (by decide)).trans h.starts
 · exact (keep 6665 (by decide)).trans h.durations
 · exact (keep 6666 (by decide)).trans h.root
 · exact (keep 6669 (by decide)).trans h.one
 · exact (keep 6670 (by decide)).trans h.two
 · exact (keep 6671 (by decide)).trans h.seven
 · exact (keep 6672 (by decide)).trans h.four
 · exact (keep 6673 (by decide)).trans h.fourteen
 · exact (keep 6679 (by decide)).trans h.zero
 · exact (keep 6680 (by decide)).trans h.ordinal
 · exact (keep 6681 (by decide)).trans h.divisor
 · exact (keep 5602 (by decide)).trans h.forward
 · exact (keep 5603 (by decide)).trans h.transpose
 · exact (keep 6693 (by decide)).trans h.ranges
lemma withPC {p:Parameters}{visits:List Visit}{i:ℕ}{s:State}(h:Control p visits i s)(pc:ℕ):
 Control p visits i (setPC s pc):=transport h (fun _ _=>rfl)
lemma cursor {p:Parameters}{visits:List Visit}{i:ℕ}{s:State}
 (h:Control p visits i s)(core:Core (position p visits i) s):Cursor p visits i s:=
 ⟨core,h.nodes,h.count,h.index,h.pointer,h.starts,h.durations,h.root,h.one,h.two,h.seven,h.four,h.fourteen,h.zero,h.ordinal,h.divisor,h.forward,h.transpose,h.ranges⟩
lemma forward {p:Parameters}{visits:List Visit}{i:ℕ}{s:State}
 (h:Control p visits i s):Control p visits i (UniformDirectLeafForestForward.result s):=by
 apply transport h
 intro j hj
 simp only[registers,List.mem_cons,List.not_mem_nil,or_false] at hj
 rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals simp [UniformDirectLeafForestForward.result,UniformDirectLeafForestProgram.forward,
  applyBlock,Op.apply,writeNat,next]
lemma produced {p:Parameters}{visits:List Visit}{i n B t:ℕ}{x:Fin n→ℂ}{s u:State}
 (h:Control p visits i s)(run:BoundedExecution UniformDirectLeafCacheLeafProgram.program n x B s t u):
 Control p visits i u:=by
 apply transport h
 intro j hj
 by_cases low:j=5602∨j=5603
 · exact UniformDirectLeafHighFrames.execution_nat run j (by omega)
 · apply UniformDirectLeafCacheLoopFrames.execution_nat run j
   · simp only[registers,List.mem_cons,List.not_mem_nil,or_false] at hj
     omega
   · simp only[registers,List.mem_cons,List.not_mem_nil,or_false] at hj
     omega
end
end ExactFourierCircuits.UniformDirectLeafForestControl

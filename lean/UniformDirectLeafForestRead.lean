import UniformDirectLeafForestData
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestRead
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafForestData
open UniformLocalCacheTreeMachine UniformLocalCacheTreeIteration
noncomputable section

def result(s:State):State:=applyBlock UniformDirectLeafForestProgram.read s
lemma cursor {p:Parameters}{visits:List Visit}{i:ℕ}{q:Visit}{s:State}
 (h:Cursor p visits i s)(node:AtNode p.nodes i q.task q.rectangleBase s)
 (start:s.natHeap (p.starts+i)=some 0):ReadCursor p visits i q (result s):=by
 have h0:=node (0:Fin 7)
 have h2:=node (2:Fin 7)
 change s.natHeap (p.nodes+7*i+0)=some q.task.width at h0
 change s.natHeap (p.nodes+7*i+2)=some (UniformWorkspacePlanner.selected q.task.width) at h2
 simp only[Nat.add_zero] at h0
 constructor
 · constructor
   · constructor <;>simp [result,UniformDirectLeafForestProgram.read,applyBlock,Op.apply,writeNat,next,
     h.originalDirectory,h.conjugateDirectory,h.pool,h.rows,h.permutation,h.widths,h.markers,h.axis,h.entry]
   all_goals simp [result,UniformDirectLeafForestProgram.read,applyBlock,Op.apply,writeNat,next,
    h.nodes,h.count,h.index,h.pointer,h.starts,h.durations,h.root,h.one,h.two,h.seven,h.four,
    h.fourteen,h.zero,h.ordinal,h.divisor,h.forward,h.transpose,h.ranges]
 all_goals simp [result,UniformDirectLeafForestProgram.read,applyBlock,Op.apply,writeNat,next,
  h.pointer,h.two,h.starts,h.index,h0,h2,start]

lemma frame (s:State):(result s).natHeap=s.natHeap ∧(result s).scalarHeap=s.scalarHeap ∧
 (result s).scalarReg=s.scalarReg ∧(result s).outputs=s.outputs ∧(result s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl,rfl⟩
lemma pc (s:State):(result s).pc=s.pc+5:=applyBlock_pc _ _

theorem execution {p:Parameters}{visits:List Visit}{i n B:ℕ}{q:Visit}(x:Fin n→ℂ)(s:State)
 (h:Cursor p visits i s)(node:AtNode p.nodes i q.task q.rectangleBase s)
 (start:s.natHeap (p.starts+i)=some 0)(code:461≤B)(hp:s.pc=32)(wb:WordBound B s):
 BoundedRuns UniformDirectLeafForestProgram.program n x B s 5 (result s):=by
 have h0:=node (0:Fin 7)
 have h2:=node (2:Fin 7)
 change s.natHeap (p.nodes+7*i+0)=some q.task.width at h0
 change s.natHeap (p.nodes+7*i+2)=some (UniformWorkspacePlanner.selected q.task.width) at h2
 simp only[Nat.add_zero] at h0
 have hd:s.natHeap (s.natReg 6663)=some q.task.width:=by rw[h.pointer];exact h0
 have hs:s.natHeap (s.natReg 6663+2)=some (UniformWorkspacePlanner.selected q.task.width):=by
  rw[h.pointer];exact h2
 have ht:s.natHeap (s.natReg 6664+s.natReg 6662)=some 0:=by rw[h.starts,h.index];exact start
 have b0:=(wb.2.2.1 _ _ hd).2
 have b2:=(wb.2.2.1 _ _ hs)
 have bt:=(wb.2.2.1 _ _ ht).1
 apply block_runs UniformDirectLeafForestProgram.read UniformDirectLeafForestProgram.program 32 n B x s
  UniformDirectLeafForestProgram.read_code hp wb (by change 37≤B;omega)
 · simp [UniformDirectLeafForestProgram.read,readable,Op.readable,Op.apply,writeNat,next,h.two,hd,hs,ht]
 · simp [UniformDirectLeafForestProgram.read,peak,Op.peak,Op.apply,writeNat,next,h.two,hd,hs,ht]
   omega
end
end ExactFourierCircuits.UniformDirectLeafForestRead

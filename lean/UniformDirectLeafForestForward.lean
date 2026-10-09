import UniformDirectLeafForestRead
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestForward
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafForestData
open UniformDirectLeafCacheReader UniformLocalCacheTreeMachine
noncomputable section

def config(p:Parameters)(visits:List Visit)(i:ℕ):Config:=
 {position p visits i with record:=p.forward,time:=0}
def result(s:State):State:=applyBlock UniformDirectLeafForestProgram.forward s
lemma args {p:Parameters}{visits:List Visit}{i:ℕ}{q:Visit}{s:State}
 (h:ReadCursor p visits i q s):Args (config p visits i) (result s):=by
 constructor <;>simp [result,UniformDirectLeafForestProgram.forward,applyBlock,Op.apply,writeNat,next,
  config,h.originalDirectory,h.conjugateDirectory,h.pool,h.rows,h.permutation,h.widths,h.markers,h.axis,h.entry,
  h.forward,h.start,h.pointer,h.zero]
lemma header {p:Parameters}{visits:List Visit}{i:ℕ}{q:Visit}{s:State}
 (h:ReadCursor p visits i q s):
 (result s).natReg 5600=p.nodes+7*i ∧(result s).natReg 5602=p.forward ∧
 (result s).natReg 5603=p.transpose ∧(result s).natReg 6611=0 ∧
 (result s).natReg 6675=q.task.width+14*q.task.width*(q.task.width-1):=by
 simp [result,UniformDirectLeafForestProgram.forward,applyBlock,Op.apply,writeNat,next,
  h.pointer,h.forward,h.transpose,h.width,h.one,h.fourteen,h.zero,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]
lemma frame(s:State):(result s).natHeap=s.natHeap ∧(result s).scalarHeap=s.scalarHeap ∧
 (result s).scalarReg=s.scalarReg ∧(result s).outputs=s.outputs ∧(result s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl,rfl⟩
lemma pc(s:State):(result s).pc=s.pc+9:=applyBlock_pc _ _

theorem execution {p:Parameters}{visits:List Visit}{i n B:ℕ}{q:Visit}(x:Fin n→ℂ)(s:State)
 (h:ReadCursor p visits i q s)
 (duration:q.task.width+14*q.task.width*(q.task.width-1)≤B)(_root:p.rootDuration+4≤B)
 (code:461≤B)(hp:s.pc=39)(wb:WordBound B s):
 BoundedRuns UniformDirectLeafForestProgram.program n x B s 9 (result s):=by
 have pointer:=wb.2.1 6663
 have forward:=wb.2.1 5602
 have width:=wb.2.1 6667
 rw[h.width] at width
 have product:q.task.width*(q.task.width-1)≤B:=by nlinarith only[duration]
 have combined:q.task.width+14*(q.task.width*(q.task.width-1))≤B:=by
  simpa only[Nat.mul_assoc] using duration
 have scaled:14*(q.task.width*(q.task.width-1))≤B:=by nlinarith only[duration]
 apply block_runs UniformDirectLeafForestProgram.forward UniformDirectLeafForestProgram.program 39 n B x s
  UniformDirectLeafForestProgram.forward_code hp wb (by change 48≤B;omega)
 · simp [UniformDirectLeafForestProgram.forward,readable,Op.readable]
 · simp [UniformDirectLeafForestProgram.forward,peak,Op.peak,Op.apply,writeNat,next,
    h.zero,h.width,h.one,h.fourteen,h.start]
   omega
end
end ExactFourierCircuits.UniformDirectLeafForestForward

import UniformDirectLeafForestCapture
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestAdvance
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafForestData UniformDirectLeafForestControl
open UniformLocalCacheTreeMachine
noncomputable section

def advanced(s:State):State:=setPC (applyBlock UniformDirectLeafForestProgram.advance s) 31
lemma frame(s:State):(advanced s).natHeap=s.natHeap ∧(advanced s).scalarHeap=s.scalarHeap ∧
 (advanced s).scalarReg=s.scalarReg ∧(advanced s).outputs=s.outputs ∧(advanced s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl,rfl⟩
lemma core {c:UniformDirectLeafCacheReader.Config}{s:State}(h:Core c s):Core c (advanced s):=by
 constructor <;>simp [advanced,UniformDirectLeafForestProgram.advance,applyBlock,Op.apply,writeNat,next,setPC,
  h.originalDirectory,h.conjugateDirectory,h.pool,h.rows,h.permutation,h.widths,h.markers,h.axis,h.entry]

theorem execution {n B:ℕ}(x:Fin n→ℂ)(s:State)
 (seven:s.natReg 6671=7)(one:s.natReg 6669=1)
 (pointer:s.natReg 6663+7≤B)(index:s.natReg 6662+1≤B)
 (code:461≤B)(pc:s.pc=450)(wb:WordBound B s):
 BoundedRuns UniformDirectLeafForestProgram.program n x B s 3 (advanced s):=by
 let a:=applyBlock UniformDirectLeafForestProgram.advance s
 have run:BoundedRuns UniformDirectLeafForestProgram.program n x B s 2 a:=by
  apply block_runs UniformDirectLeafForestProgram.advance UniformDirectLeafForestProgram.program 450 n B x s
   UniformDirectLeafForestProgram.advance_code pc wb (by change 452≤B;omega)
  · simp [UniformDirectLeafForestProgram.advance,readable,Op.readable]
  · simp [UniformDirectLeafForestProgram.advance,peak,Op.peak,Op.apply,writeNat,next,seven,one]
    omega
 have ap:a.pc=452:=by rw[applyBlock_pc,pc,UniformDirectLeafForestProgram.advance_length]
 have bound:=changePC_bound B a 31 run.final_bound (by omega)
 have jump:BoundedRuns UniformDirectLeafForestProgram.program n x B a 1 (advanced s):=
  .next run.final_bound (by simp [UniformMachine.step,ap,UniformDirectLeafForestProgram.next_at,advanced,a,setPC])
  (.refl bound)
 simpa using run.trans jump

lemma captured_control {p:Parameters}{visits:List Visit}{i N:ℕ}{s:State}
 (h:Control p visits i s)(count:s.natReg 6628=N)
 (following:UniformDirectLeafForestModel.before visits (i+1)=UniformDirectLeafForestModel.before visits i+N):
 Control p visits (i+1) (advanced (setPC (UniformDirectLeafForestCapture.captured s) 450)):=by
 constructor <;>simp [advanced,UniformDirectLeafForestCapture.captured,
  UniformDirectLeafForestProgram.capture,UniformDirectLeafForestProgram.advance,
  applyBlock,Op.apply,writeNat,next,setPC,
  h.nodes,h.count,h.index,h.pointer,h.starts,h.durations,h.root,h.one,h.two,h.seven,h.four,
  h.fourteen,h.zero,h.ordinal,h.divisor,h.forward,h.transpose,h.ranges,count,following,
  Nat.mul_add,Nat.add_assoc]
end
end ExactFourierCircuits.UniformDirectLeafForestAdvance

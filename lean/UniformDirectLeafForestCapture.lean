import UniformDirectLeafForestControl
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestCapture
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafForestData UniformDirectLeafForestControl
open UniformLocalCacheTreeMachine
noncomputable section

def captured(s:State):State:=applyBlock UniformDirectLeafForestProgram.capture s
def outputHeap(h:ℕ→Option ℕ)(R i first count:ℕ):ℕ→Option ℕ:=
 Function.update (Function.update h (R+2*i) (some first)) (R+2*i+1) (some count)
lemma heap {p:Parameters}{visits:List Visit}{i N first:ℕ}{s:State}
 (h:Control p visits i s)(count:s.natReg 6628=N)(stride:s.natReg 6634=3*p.radix+11)
 (entry:s.natReg 6609=first+(3*p.radix+11)*N):
 (captured s).natHeap=outputHeap s.natHeap p.ranges i first N:=by
 simp [captured,UniformDirectLeafForestProgram.capture,applyBlock,Op.apply,writeNat,next,
  h.index,h.two,h.ranges,h.one,count,stride,entry,outputHeap,Nat.mul_comm]
lemma value {p:Parameters}{visits:List Visit}{i N first:ℕ}{s:State}
 (h:Control p visits i s)(count:s.natReg 6628=N)(stride:s.natReg 6634=3*p.radix+11)
 (entry:s.natReg 6609=first+(3*p.radix+11)*N):
 (captured s).natHeap (p.ranges+2*i)=some first ∧
 (captured s).natHeap (p.ranges+2*i+1)=some N:=by
 rw[heap h count stride entry]
 simp [outputHeap]
lemma outside {p:Parameters}{visits:List Visit}{i N first:ℕ}{s:State}
 (h:Control p visits i s)(count:s.natReg 6628=N)(stride:s.natReg 6634=3*p.radix+11)
 (entry:s.natReg 6609=first+(3*p.radix+11)*N)(a:ℕ)
 (out:a<p.ranges+2*i ∨p.ranges+2*i+2≤a):
 (captured s).natHeap a=s.natHeap a:=by
 rw[heap h count stride entry]
 simp (disch:=omega) [outputHeap]
lemma frame(s:State):(captured s).scalarHeap=s.scalarHeap ∧(captured s).scalarReg=s.scalarReg ∧
 (captured s).outputs=s.outputs ∧(captured s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl⟩
lemma core {c:UniformDirectLeafCacheReader.Config}{s:State}(h:Core c s):Core c (captured s):=by
 constructor <;>simp [captured,UniformDirectLeafForestProgram.capture,applyBlock,Op.apply,writeNat,next,
  h.originalDirectory,h.conjugateDirectory,h.pool,h.rows,h.permutation,h.widths,h.markers,h.axis,h.entry]

theorem execution {p:Parameters}{visits:List Visit}{i N first n B:ℕ}(x:Fin n→ℂ)(s:State)
 (h:Control p visits i s)(count:s.natReg 6628=N)(stride:s.natReg 6634=3*p.radix+11)
 (entry:s.natReg 6609=first+(3*p.radix+11)*N)(index:i<visits.length)
 (range:p.ranges+2*visits.length≤B)(ordinal:p.rectangles+UniformDirectLeafForestModel.before visits i+N≤B)
 (code:461≤B)(pc:s.pc=436)(wb:WordBound B s):
 BoundedRuns UniformDirectLeafForestProgram.program n x B s 8 (captured s):=by
 have eb:=wb.2.1 6609
 rw[entry] at eb
 have mult:N*(3*p.radix+11)≤B:=by nlinarith only[eb]
 have mult':N*(p.radix*3+11)≤B:=by simpa only[Nat.mul_comm p.radix 3] using mult
 have two:2*i+1<2*visits.length:=by omega
 apply block_runs UniformDirectLeafForestProgram.capture UniformDirectLeafForestProgram.program 436 n B x s
  UniformDirectLeafForestProgram.capture_code pc wb (by change 444≤B;omega)
 · simp [UniformDirectLeafForestProgram.capture,readable,Op.readable]
 · simp [UniformDirectLeafForestProgram.capture,peak,Op.peak,Op.apply,writeNat,next,
    h.index,h.two,h.ranges,h.one,h.ordinal,count,stride,entry,Nat.mul_comm]
   omega
end
end ExactFourierCircuits.UniformDirectLeafForestCapture

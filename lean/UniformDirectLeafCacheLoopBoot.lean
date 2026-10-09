import UniformDirectLeafCacheLoopData
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheLoopBoot
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafCacheReader
open UniformDirectLeafCacheLoopProgram UniformDirectLeafCacheLoopData
noncomputable section

def size (v:ℕ):ℕ:=v+v*(v-1)/2
def left (s:State):State:=applyBlock bootLeft s
def divided (s:State):State:=writeNat (left s) 6628 ((left s).natReg 6628/2)
def initialized (s:State):State:=applyBlock bootRight (divided s)

lemma left_values {c:Config} {v:ℕ} {s:State} (_args:Args c s)
 (width:s.natHeap (s.natReg 5600)=some v):
 (left s).natReg 6627=v ∧(left s).natReg 6628=v*(v-1) ∧(left s).natReg 6622=2:=by
 simp [left,bootLeft,applyBlock,Op.apply,writeNat,next,width]
lemma initialized_controls {c:Config} {v r:ℕ} {s:State} (args:Args c s)
 (width:s.natHeap (s.natReg 5600)=some v)
 (radix:s.natHeap (c.originalDirectory+1)=some r):Controls r (size v) 0 (initialized s):=by
 constructor <;>simp [initialized,divided,left,bootLeft,bootRight,applyBlock,Op.apply,
  writeNat,next,width,args.originalDirectory,radix,size,Nat.add_comm,Nat.mul_comm]
lemma initialized_args {c:Config} {s:State} (args:Args c s):Args c (initialized s):=by
 constructor <;>simp [initialized,divided,left,bootLeft,bootRight,applyBlock,Op.apply,writeNat,next,
  args.record,args.originalDirectory,args.conjugateDirectory,args.pool,args.rows,args.permutation,
  args.widths,args.markers,args.axis,args.entry,args.time]
lemma initialized_frame (s:State):(initialized s).natHeap=s.natHeap ∧
 (initialized s).scalarHeap=s.scalarHeap ∧(initialized s).scalarReg=s.scalarReg ∧
 (initialized s).outputs=s.outputs ∧(initialized s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl,rfl⟩
lemma initialized_nat (s:State) (j:ℕ) (outside:j<6620∨6635≤j):
 (initialized s).natReg j=s.natReg j:=by
 simp (disch:=omega) [initialized,divided,left,bootLeft,bootRight,applyBlock,Op.apply,writeNat,next]

/-- Even the division by two and the transient undivided quadratic count are
charged and covered by the common word bound. -/
theorem boot_execution {c:Config} {v r n B:ℕ} (x:Fin n→ℂ) (s:State)
 (args:Args c s) (width:s.natHeap (s.natReg 5600)=some v)
 (radix:s.natHeap (c.originalDirectory+1)=some r)
 (count:size v≤B) (quadratic:v*(v-1)≤B) (ss:9*r≤B) (ns:3*r+11≤B)
 (code:303≤B) (pc:s.pc=0) (wb:WordBound B s):
 BoundedRuns UniformDirectLeafCacheLoopProgram.program n x B s 19 (initialized s):=by
 have vw:v≤B:=(wb.2.2.1 _ _ width).2
 have rb:r≤B:=(wb.2.2.1 _ _ radix).2
 have db:c.originalDirectory+1≤B:=(wb.2.2.1 _ _ radix).1
 have lw:=left_values args width
 have lrun:BoundedRuns UniformDirectLeafCacheLoopProgram.program n x B s 10 (left s):=by
  apply block_runs bootLeft UniformDirectLeafCacheLoopProgram.program 0 n B x s bootLeft_code pc wb (by change 10≤B;omega)
  · simp [bootLeft,readable,Op.readable,Op.apply,writeNat,next,width]
  · simp [bootLeft,peak,Op.peak,Op.apply,writeNat,next,width]
    omega
 have lp:(left s).pc=10:=by rw[left,applyBlock_pc,pc];rfl
 have dw:WordBound B (divided s):=writeNat_bound B (left s) 6628 _ lrun.final_bound
  (by rw[lp];omega) (by rw[lw.2.1];exact (Nat.div_le_self _ _).trans quadratic)
 have drun:BoundedRuns UniformDirectLeafCacheLoopProgram.program n x B (left s) 1 (divided s):=.next lrun.final_bound
  (by simp [UniformMachine.step,lp,boot_div,lw.2.1,lw.2.2,evalNat,divided]) (.refl dw)
 have dp:(divided s).pc=11:=by simp[divided,writeNat,next,lp]
 have rrun:BoundedRuns UniformDirectLeafCacheLoopProgram.program n x B (divided s) 8 (initialized s):=by
  apply block_runs bootRight UniformDirectLeafCacheLoopProgram.program 11 n B x (divided s) bootRight_code dp dw (by change 19≤B;omega)
  · simp [bootRight,readable,Op.readable,Op.apply,writeNat,next,divided,left,bootLeft,
    applyBlock,width,args.originalDirectory,radix]
  · simp [bootRight,peak,Op.peak,Op.apply,writeNat,next,divided,left,bootLeft,
    applyBlock,width,args.originalDirectory,radix]
    have mul:3*r≤B:=by omega
    have nine:r*9≤B:=by simpa[Nat.mul_comm] using ss
    have three:r*3+11≤B:=by simpa[Nat.mul_comm] using ns
    change v+v*(v-1)/2≤B at count
    omega
 convert (lrun.trans drun).trans rrun using 1

end
end ExactFourierCircuits.UniformDirectLeafCacheLoopBoot

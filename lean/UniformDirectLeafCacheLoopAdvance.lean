import UniformDirectLeafCacheLoopData
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheLoopAdvance
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafCacheReader
open UniformDirectLeafCacheLoopProgram UniformDirectLeafCacheLoopData UniformDirectLeafCacheChronology
open UniformTransposeDescriptorMachine (Record)
noncomputable section

def advanced (s:State):State:=setPC (applyBlock advance s) 23
lemma advance_args {c:Config} {r N i:ℕ} {q:Record} {s:State}
 (args:Args {c with time:=c.time+duration q} s) (control:Controls r N i s):
 Args (nextConfig c r q) (advanced s) := by
 rcases args with ⟨a,b,c',d,e,f,g,h,j,k,l⟩
 rcases control with ⟨z,one,four,_N,idx,_tick,ss,ns⟩
 constructor <;>simp [advanced,advance,applyBlock,Op.apply,writeNat,next,setPC,
  nextConfig,a,b,c',d,e,f,g,h,j,k,l,one,four,ss,ns]
lemma advance_controls {r N i:ℕ} {s:State} (h:Controls r N i s):Controls r N (i+1) (advanced s):=by
 rcases h with ⟨z,one,four,count,idx,tick,ss,ns⟩
 constructor <;>simp [advanced,advance,applyBlock,Op.apply,writeNat,next,setPC,z,one,four,count,idx,tick,ss,ns]
lemma advance_frame (s:State): (advanced s).natHeap=s.natHeap ∧
 (advanced s).scalarHeap=s.scalarHeap ∧(advanced s).scalarReg=s.scalarReg ∧
 (advanced s).outputs=s.outputs ∧(advanced s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl,rfl⟩
lemma advance_nat (s:State) (j:ℕ) (outside:j<6600∨6630≤j):
 (advanced s).natReg j=s.natReg j:=by
 simp (disch:=omega) [advanced,advance,applyBlock,Op.apply,writeNat,next,setPC]
lemma advance_bounded {c:Config} {r N i n B:ℕ} {q:Record} (x:Fin n→ℂ) (s:State)
 (args:Args {c with time:=c.time+duration q} s) (control:Controls r N i s)
 (fit:Fits (nextConfig c r q) B) (index:i+1≤B) (pc:s.pc=293) (code:303≤B) (wb:WordBound B s):
 BoundedRuns UniformDirectLeafCacheLoopProgram.program n x B s 9 (advanced s):=by
 have f0:=fit.record;have f1:=fit.pool;have f2:=fit.permutation
 have f3:=fit.widths;have f4:=fit.markers;have f5:=fit.axis;have f6:=fit.entry
 rcases args with ⟨a,b,c',d,e,f,g,h,j,k,l⟩
 rcases control with ⟨z,one,four,count,idx,tick,ss,ns⟩
 have safe:readable advance s∧peak advance s≤B:=by
  constructor
  · simp [advance,readable,Op.readable]
  · simp [advance,peak,Op.peak,Op.apply,writeNat,next,a,d,f,g,h,j,k,one,four,idx,ss,ns]
    simp only[nextConfig] at f0 f1 f2 f3 f4 f5 f6
    omega
 have body:=block_runs advance UniformDirectLeafCacheLoopProgram.program 293 n B x s advance_code pc wb
  (by rw[advance_length];omega) safe.1 safe.2
 have bp:(applyBlock advance s).pc=301:=by rw[applyBlock_pc,advance_length,pc]
 have ub:=changePC_bound B (applyBlock advance s) 23 body.final_bound (by omega)
 have tail:BoundedRuns UniformDirectLeafCacheLoopProgram.program n x B (applyBlock advance s) 1 (advanced s):=
  .next body.final_bound (by rw[UniformMachine.step,bp,loop_jump];rfl) (.refl ub)
 simpa only[advance_length] using body.trans tail

/-- Both branches read the real emitted descriptor kind before advancing the
clock; no host event time or post-helper scratch read is assumed. -/
theorem clock {c:Config} {r N i n B:ℕ} {q:Record} (x:Fin n→ℂ) (s:State)
 (args:Args c s) (control:Controls r N i s)
 (source:s.natHeap c.record=some q.kind) (bound:c.time+duration q≤B)
 (pc:s.pc=288) (code:303≤B) (wb:WordBound B s):∃u,
 BoundedRuns UniformDirectLeafCacheLoopProgram.program n x B s (if q.kind=0 then 4 else 3) u ∧u.pc=293 ∧
 Args {c with time:=c.time+duration q} u ∧Controls r N i u ∧
 u.natHeap=s.natHeap ∧u.scalarHeap=s.scalarHeap ∧u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀j,j≠6610→j≠6635→u.natReg j=s.natReg j):=by
 let a:=applyBlock readKind s
 have read:BoundedRuns UniformDirectLeafCacheLoopProgram.program n x B s 1 a:=by
  have kindBound: q.kind≤B:=(wb.2.2.1 c.record q.kind source).2
  exact block_runs readKind UniformDirectLeafCacheLoopProgram.program 288 n B x s kind_code pc wb (by change 289≤B;omega)
   (by simp [readKind,readable,Op.readable,args.record,source])
   (by simp [readKind,peak,Op.peak,args.record,source];exact kindBound)
 have ap:a.pc=289:=by rw[applyBlock_pc,pc];rfl
 have ak:a.natReg 6635=q.kind:=by simp [a,readKind,applyBlock,Op.apply,writeNat,next,args.record,source]
 have ar (j:ℕ) (ne:j≠6635):a.natReg j=s.natReg j:=by
  simp [a,readKind,applyBlock,Op.apply,writeNat,next,ne]
 by_cases kind:q.kind=0
 · let b:=setPC a 290
   have bb:=changePC_bound B a 290 read.final_bound (by omega)
   have branch:BoundedRuns UniformDirectLeafCacheLoopProgram.program n x B a 1 b:=.next read.final_bound
    (by simp [UniformMachine.step,ap,time_branch,ak,kind,ar 6621 (by omega),control.one,b,setPC]) (.refl bb)
   let d:=applyBlock scaleTime b
   have body:BoundedRuns UniformDirectLeafCacheLoopProgram.program n x B b 1 d:=by
    apply block_runs scaleTime UniformDirectLeafCacheLoopProgram.program 290 n B x b scale_code rfl bb (by change 291≤B;omega)
    · simp [scaleTime,readable,Op.readable]
    · simp [scaleTime,peak,Op.peak,b,setPC,ar 6610 (by omega),ar 6621 (by omega),args.time,control.one]
      simpa [duration,kind] using bound
   let u:=setPC d 293
   have dp:d.pc=291:=by rw[applyBlock_pc];rfl
   have ub:=changePC_bound B d 293 body.final_bound (by omega)
   have jump:BoundedRuns UniformDirectLeafCacheLoopProgram.program n x B d 1 u:=.next body.final_bound
    (by rw[UniformMachine.step,dp,time_jump];rfl) (.refl ub)
   refine ⟨u,?_,rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,?_⟩
   · simpa only[kind,ite_true] using (read.trans branch).trans (body.trans jump)
   · constructor <;>simp [u,d,b,a,setPC,scaleTime,readKind,applyBlock,Op.apply,writeNat,next,
      args.record,args.originalDirectory,args.conjugateDirectory,args.pool,args.rows,args.permutation,
      args.widths,args.markers,args.axis,args.entry,args.time,control.one,duration,kind]
   · constructor <;>simp [u,d,b,a,setPC,scaleTime,readKind,applyBlock,Op.apply,writeNat,next,
      control.zero,control.one,control.four,control.count,control.index,control.tick,
      control.scalarStride,control.natStride]
   · intro j ne nk;simp [u,d,b,a,setPC,scaleTime,readKind,applyBlock,Op.apply,writeNat,next,ne,nk]
 · let b:=setPC a 292
   have bb:=changePC_bound B a 292 read.final_bound (by omega)
   have branch:BoundedRuns UniformDirectLeafCacheLoopProgram.program n x B a 1 b:=.next read.final_bound
    (by simp [UniformMachine.step,ap,time_branch,ak,ar 6621 (by omega),control.one,b,setPC,show ¬q.kind<1 by omega]) (.refl bb)
   let u:=applyBlock shearTime b
   have body:BoundedRuns UniformDirectLeafCacheLoopProgram.program n x B b 1 u:=by
    apply block_runs shearTime UniformDirectLeafCacheLoopProgram.program 292 n B x b shear_code rfl bb (by change 293≤B;omega)
    · simp [shearTime,readable,Op.readable]
    · simp [shearTime,peak,Op.peak,b,setPC,ar 6610 (by omega),ar 6630 (by omega),args.time,control.tick]
      simpa [duration,kind] using bound
   refine ⟨u,?_,?_,?_,?_,rfl,rfl,rfl,rfl,rfl,?_⟩
   · simpa only[kind,ite_false] using (read.trans branch).trans body
   · rw[applyBlock_pc];rfl
   · constructor <;>simp [u,b,a,setPC,shearTime,readKind,applyBlock,Op.apply,writeNat,next,
      args.record,args.originalDirectory,args.conjugateDirectory,args.pool,args.rows,args.permutation,
      args.widths,args.markers,args.axis,args.entry,args.time,control.tick,duration,kind]
   · constructor <;>simp [u,b,a,setPC,shearTime,readKind,applyBlock,Op.apply,writeNat,next,
      control.zero,control.one,control.four,control.count,control.index,control.tick,
      control.scalarStride,control.natStride]
   · intro j ne nk;simp [u,b,a,setPC,shearTime,readKind,applyBlock,Op.apply,writeNat,next,ne,nk]
end
end ExactFourierCircuits.UniformDirectLeafCacheLoopAdvance
